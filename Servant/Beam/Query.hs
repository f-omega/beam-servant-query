>{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Common query language handling
module Servant.Beam.Query where

import           Control.Exception

import           Data.Aeson (Value(..), ToJSON(..), object, (.=), (.:), (.:?), (.!=))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.Types as Aeson
import           Data.Coerce (coerce)
import qualified Data.HashMap.Strict as HM
import           Data.Int (Int32)
import           Data.Kind (Type)
import           Data.Monoid (Ap(..), Alt(..))
import           Data.Proxy (Proxy(Proxy))
import           Data.String (fromString)
import           Data.Text (Text)
import qualified Data.Text.Encoding.Base64.URL as B64
import qualified Data.Text.Lazy as T (fromStrict, toStrict)
import qualified Data.Text.Lazy.Encoding as TE
import           Data.Time (LocalTime)
import           Data.Vector (Vector)

import           Database.Beam
import           Database.Beam.Backend.SQL (BeamSqlBackendCanSerialize)
import           Database.Beam.Postgres

import           Network.Wai

import           Servant.API
import           Servant.Client
import           Servant.Client.Core (RunClient)
import           Servant.Server
import           Servant.Server.Internal.Delayed
import           Servant.Server.Internal.DelayedIO

data Query db entity

data DescribeQueryableException where
  DescribeQueryableException :: HasQuery db entity => Proxy db -> Proxy entity -> DescribeQueryableException
deriving instance Exception DescribeQueryableException
deriving instance Show DescribeQueryableException

instance ( RunClient m, HasClient m (QueryParam "q" SearchBuilder :> x) )
    => HasClient m (Query db entity :> x) where
  type Client m (Query db entity :> x) = Client m (QueryParam "q" SearchBuilder :> x)

  clientWithRoute m _ = clientWithRoute m (Proxy @(QueryParam "q" SearchBuilder :> x))
  hoistClientMonad m _ = hoistClientMonad m (Proxy @(QueryParam "q" SearchBuilder :> x))

instance ( HasServer (QueryParam "q" (Search db entity)  :> x) context
         , Typeable entity, Typeable db
         , HasQuery db entity)
    => HasServer (Query db entity :> x) context where

  type ServerT (Query db entity :> x) m = ServerT (QueryParam "q" (Search db entity) :> x) m

  route (_ :: Proxy (Query db entity :> x)) ctxt dServer = do
    route (Proxy @(QueryParam "q" (Search db entity) :> x)) ctxt
          (addMethodCheck dServer optionsCheck)
    where
      optionsCheck = withRequest $ \req ->
                     if requestMethod req == "PROPFIND"
                     then liftIO (throwIO (DescribeQueryableException (Proxy @db) (Proxy @entity)))
                     else pure ()

  hoistServerWithContext (_ :: Proxy (Query db entity :> x)) =
    hoistServerWithContext (Proxy @(QueryParam "q" (Search db entity) :> x))

instance HasLink x => HasLink (Query db entity :> x) where
  type MkLink (Query db entity :> x) a = Maybe Text -> MkLink x a

  toLink mkLink _ link =
      toLink mkLink (Proxy :: Proxy (QueryParam "q" Text :> x)) link

newtype QueryParseError = QueryParseError String
  deriving (Show)
  deriving anyclass (Exception)

class HasQuery (db :: (Type -> Type) -> Type) entity where
  -- | Get a list of queryable fields for this entity
  queryableFields :: [ QueryField db entity ]

class HasTable db entity where
  -- | Get entity
  entityTable :: Q Postgres db s (QExprTable Postgres s entity)

data QueryField db entity where
  QueryField :: (Aeson.FromJSON a, BeamSqlBackendCanSerialize Postgres a)
             => { qfName        :: Text
                , qfHumanName   :: Text
                , qfDescription :: Text
                , qfParser      :: QueryParser a
                , qfGet         :: forall s. entity (QExpr Postgres s) -> QExpr Postgres s a
                } -> QueryField db entity

encodeQueryFieldJSON :: QueryField db a -> (Aeson.Key, Aeson.Value)
encodeQueryFieldJSON QueryField { qfName = nm
                                , qfHumanName = human
                                , qfDescription = desc
                                , qfParser = ps } =
  Key.fromText nm .=
     object [ "name" .= human
            , "description" .= desc
            , "type" .= parserKind ps
            , "detail" .= parserDetail ps
            , "comparisons" .= map comparisonKind (comparisons ps) ]

encodeQueryFieldsJSON :: [QueryField db a] -> Aeson.Value
encodeQueryFieldsJSON = object . map encodeQueryFieldJSON

data QueryParser a
  = QueryParser
  { parserKind    :: Text
  , parserDetail  :: Value
  , comparisons   :: [Comparison a]
  , applyKeywords :: [Text] -> FieldFilter a
  }

mapQueryParser :: (forall s. QExpr Postgres s a -> QExpr Postgres s b)
               -> QueryParser b -> QueryParser a
mapQueryParser fn ps =
  ps { comparisons = fmap (mapComparison fn) (comparisons ps)
     , applyKeywords = \kws -> mapFieldFilter fn (applyKeywords ps kws)
     }

maybeQueryParser :: forall a. QueryParser a -> QueryParser (Maybe a)
maybeQueryParser qp =
  qp { comparisons = isNothingComp:map liftComparison (comparisons qp)
     , applyKeywords = \ks -> liftFieldFilter (applyKeywords qp ks)
     }

  where
    isNothingComp :: Comparison (Maybe a)
    isNothingComp = Comparison { comparisonKind = "is_nothing"
                               , comparisonParser = Aeson.withObject "is_just" $ \v -> do
                                                      True <- v .: "is_just"
                                                      pure (FieldFilter (sqlBool_ . isJust_)) }

    liftComparison :: Comparison a -> Comparison (Maybe a)
    liftComparison c = c { comparisonParser = \v -> fmap liftFieldFilter (comparisonParser c v) }

    liftFieldFilter :: FieldFilter a -> FieldFilter (Maybe a)
    liftFieldFilter NoFieldFilter = NoFieldFilter
    liftFieldFilter (FieldFilter f) = FieldFilter (maybe_ (sqlBool_ (val_ False)) f)

data FieldFilter a
  = FieldFilter (forall s. QExpr Postgres s a -> QExpr Postgres s SqlBool)
  | NoFieldFilter

instance Semigroup (FieldFilter a) where
  FieldFilter a <> FieldFilter b = FieldFilter (\e -> a e ||?. b e)
  NoFieldFilter <> b = b
  a <> NoFieldFilter = a

instance Monoid (FieldFilter a) where
  mempty = NoFieldFilter

mapFieldFilter :: (forall s. QExpr Postgres s a -> QExpr Postgres s b)
               -> FieldFilter b -> FieldFilter a
mapFieldFilter _ NoFieldFilter = NoFieldFilter
mapFieldFilter fn (FieldFilter x) = FieldFilter (x . fn)

data Search db entity
  = Search (forall s. entity (QExpr Postgres s) -> QExpr Postgres s SqlBool)
  | NoSearch

data SearchBuilder
  = SearchBuilder
  { sbKeywords :: [ Text ]
  , sbComparisons :: HM.HashMap Text [ Value ]
  } deriving Show

instance ToJSON SearchBuilder where
  toJSON (SearchBuilder { sbKeywords = kws, sbComparisons = comps }) =
    object ([ "keywords" .= kws | not (null kws) ] ++
            fmap (\(field, fieldComps) -> Key.fromText field .= fieldComps) (HM.toList comps))

instance Semigroup (Search db entity) where
  Search a <> Search b = Search (\e -> a e &&?. b e)
  NoSearch <> b = b
  a <> NoSearch = a

instance Monoid (Search db entity) where
  mempty = NoSearch

newtype KeywordSearch db entity
  = KeywordSearch (Search db entity)

instance Semigroup (KeywordSearch db entity) where
  KeywordSearch (Search a) <> KeywordSearch (Search b) = KeywordSearch (Search (\e -> a e ||?. b e))
  KeywordSearch NoSearch <> b = b
  a <> KeywordSearch NoSearch = a

instance Monoid (KeywordSearch db entity) where
  mempty = KeywordSearch NoSearch

instance HasQuery db entity => FromHttpApiData (Search db entity) where
  parseQueryParam txt = do
    jsonRepr <- B64.decodeBase64 txt
    let jsonReprBS = TE.encodeUtf8 (T.fromStrict jsonRepr)
    case Aeson.eitherDecode jsonReprBS of
      Left  str -> Left (fromString str)
      Right val -> pure (parseQuery val)

instance ToHttpApiData SearchBuilder where
  toQueryParam search =
    let jsonQuery = Aeson.encode search
    in toQueryParam (B64.encodeBase64 (T.toStrict (TE.decodeUtf8 jsonQuery)))

data Comparison a
  = Comparison
  { comparisonKind :: Text
  , comparisonParser :: Aeson.Value -> Aeson.Parser (FieldFilter a) }

mapComparison :: (forall s. QExpr Postgres s a -> QExpr Postgres s b)
              -> Comparison b -> Comparison a
mapComparison fn c =
  c { comparisonParser = \v -> fmap (mapFieldFilter fn) $ comparisonParser c v }

parseComparison :: Aeson.Value -> Comparison a -> Aeson.Parser (FieldFilter a)
parseComparison o Comparison { comparisonParser = parse } =
  flip (Aeson.withObject "comparison") o $ \v -> do
    condition <- parse o
    case condition of
      NoFieldFilter -> pure NoFieldFilter
      FieldFilter x -> do
        opposite <- v .:? "invert" .!= False
        pure (if opposite then FieldFilter (sqlNot_ . x) else FieldFilter x)

parseQuery :: forall entity db. HasQuery db entity => Aeson.Value -> Search db entity
parseQuery = parseQuery' (queryableFields @db @entity)

parseQuery' :: [ QueryField db entity ] -> Aeson.Value -> Search db entity
parseQuery' fields queryJson =
  case Aeson.parse (queryParser fields) queryJson of
    Aeson.Error e -> throw (QueryParseError e)
    Aeson.Success x -> x

queryParser :: [QueryField db entity] -> Value -> Aeson.Parser (Search db entity)
queryParser fields = Aeson.withObject "query" $ \v -> do
  keywords :: [ Text ] <- v .:? "keywords" .!= []

  -- Now fetch each field
  let parseField (QueryField name _humanNm _desc
                             (QueryParser { comparisons = comps
                                          , applyKeywords = mkKeywords })
                             getField) = do
        filters <- v .:? Key.fromText name .!= []
        let parser comparisonJson = getAlt (foldMap (Alt . parseComparison comparisonJson) comps)
        fullFieldFilter <- getAp (foldMap (Ap . parser) filters)
        let keywordFilter = mkKeywords keywords

            fieldSearch = case fullFieldFilter of
                            NoFieldFilter -> NoSearch
                            FieldFilter fieldFilter -> Search (fieldFilter . getField)

            keywordSearch = KeywordSearch $
                            case keywordFilter of
                              NoFieldFilter -> NoSearch
                              FieldFilter kwFilter -> Search (kwFilter . getField)

        pure (fieldSearch, keywordSearch)

  (fieldsSearch, KeywordSearch keywordSearch) <- getAp (foldMap (Ap . parseField) fields)
  pure (fieldsSearch <> keywordSearch)

filterSearch :: Maybe (Search db entity) -> (forall s'. Q Postgres db s' (entity (QExpr Postgres s')))
             -> Q Postgres db s (entity (QExpr Postgres s))
filterSearch search x = do
  q <- x
  guardSearch search q
  pure q

guardSearch :: Maybe (Search db entity)
            -> entity (QExpr Postgres s)
            -> Q Postgres db s ()
guardSearch (Just (Search find)) x = guard_' (find x)
guardSearch _ _ = pure ()

-- Field parsers
queryField :: (Aeson.FromJSON a, BeamSqlBackendCanSerialize Postgres a)
           => (forall s. entity (QExpr Postgres s) -> QExpr Postgres s a)
           -> Text -> Text -> Text -> QueryParser a -> QueryField db entity
queryField getField nm humanNm desc parser =
  QueryField { qfName = nm
             , qfHumanName = humanNm
             , qfDescription = desc
             , qfParser = parser
             , qfGet = getField }

searchableBool :: QueryParser Bool
searchableBool = QueryParser { parserKind = "bool"
                             , parserDetail = Null
                             , comparisons = [ isTrue ]
                             , applyKeywords = \_ -> mempty }

searchableForeignKey'
    :: forall tbl db
     . ( Beamable (PrimaryKey tbl)
       , SingleFieldPrimaryKey tbl
       , BeamSqlBackendCanSerialize Postgres (SingleFieldType tbl)
       , Aeson.FromJSON (SingleFieldType tbl)
       , HasSqlEqualityCheck Postgres (SingleFieldType tbl))
    => Text -> (forall s. Q Postgres db s (QExprTable Postgres s tbl))
    -> [QueryField db tbl] -> QueryParser (SingleFieldType tbl)
searchableForeignKey' entityNm tbl fields =
    QueryParser { parserKind = "foreign"
                , parserDetail = object [ "entity" .= entityNm
                                        , "searchUrl" .= searchUrl (Proxy @tbl)
                                        , "fields" .= encodeQueryFieldsJSON fields ]
                , comparisons = [ coerce (isEqualTo :: Comparison (SingleFieldType tbl))
                                , meetsCriteria tbl fields ]
                , applyKeywords = \_ -> mempty } -- TODO search

searchableForeignKey
    :: forall tbl db
     . ( Beamable (PrimaryKey tbl)
       , SingleFieldPrimaryKey tbl
       , Aeson.FromJSON (SingleFieldType tbl)
       , HasSqlEqualityCheck Postgres (SingleFieldType tbl)
       , BeamSqlBackendCanSerialize Postgres (SingleFieldType tbl)
       , HasTable db tbl
       , HasQuery db tbl )
    => Text -> QueryParser (SingleFieldType tbl)
searchableForeignKey entityNm = searchableForeignKey' entityNm (entityTable @db @tbl) (queryableFields @db @tbl)

entityId :: ( HasSqlEqualityCheck Postgres id
            , Aeson.FromJSON id
            , BeamSqlBackendCanSerialize Postgres id )
         => Text -> QueryParser id
entityId entityNm =
    QueryParser { parserKind = "id"
                , parserDetail = object [ "entity" .= entityNm ]
                , comparisons = [ isEqualTo ]
                , applyKeywords = \_ -> mempty } -- TODO search

searchableText :: QueryParser Text
searchableText = QueryParser
               { parserKind = "text"
               , parserDetail = Null
               , comparisons = [contains, beginsWith, endsWith, isEqualTo]
               , applyKeywords = doKeywords }
  where
    mkKeywordFilter txt = FieldFilter (\e -> sqlBool_ (e `like_` concat_ [ val_ "%", val_ txt, val_ "%" ]))
    doKeywords kws = foldMap mkKeywordFilter kws

filterList :: FieldFilter a -> FieldFilter (Vector a)
filterList NoFieldFilter = NoFieldFilter
filterList (FieldFilter x) = FieldFilter $ \vs ->
                               sqlBool_ $ exists_ $ do
                                 v <- pgUnnestArray vs
                                 guard_' (x v)
                                 pure (as_ @Int32 $ val_ 1)

compareList :: Comparison a -> Comparison (Vector a)
compareList c = c { comparisonParser = \v -> fmap filterList (comparisonParser c v) }

searchableList :: QueryParser a -> QueryParser (Vector a)
searchableList qp = qp { comparisons = map compareList (comparisons qp)
                       , applyKeywords = \kws -> filterList (applyKeywords qp kws) }

exactText :: QueryParser Text
exactText = QueryParser { parserKind = "text"
                        , parserDetail = Null
                        , comparisons = [ isEqualTo ]
                        , applyKeywords = doKeywords}
  where
    mkExactFilter txt = FieldFilter (==?. (val_ txt))
    doKeywords kws = foldMap mkExactFilter kws

searchableDateTime :: QueryParser LocalTime
searchableDateTime = QueryParser
                   { parserKind = "datetime"
                   , parserDetail = Null
                   , comparisons = [ isBefore, isAfter, isBetween ]
                   , applyKeywords = \_ -> mempty
                   }

searchableNumber :: ( Num a, Ord a, HasSqlEqualityCheck Postgres a
                    , BeamSqlBackendCanSerialize Postgres a
                    , Aeson.FromJSON a) => QueryParser a
searchableNumber = QueryParser
                 { parserKind = "number"
                 , parserDetail = Null
                 , comparisons = [ isBefore, isAfter, isBetween, isEqualTo ]
                 , applyKeywords = \_ -> mempty
                 }

class Table table => SingleFieldPrimaryKey table where
  type SingleFieldType table :: Type
  getSingleFieldPk :: PrimaryKey table f -> C f (SingleFieldType table)
  searchUrl :: Proxy table -> Text

-- Comparisons
isTrue :: Comparison Bool
isTrue = Comparison { comparisonKind = "is_true"
                    , comparisonParser = Aeson.withObject "is_true" $ \v -> do
                        True <- v .: "is_true"
                        pure (FieldFilter sqlBool_) }


contains, beginsWith, endsWith :: Comparison Text
contains = Comparison { comparisonKind = "contains"
                      , comparisonParser = Aeson.withObject "contains" $ \v -> do
                                             keyword <- v .: "contains"
                                             pure $ FieldFilter $ \e ->
                                                 sqlBool_ (e `like_` concat_ [val_ "%", val_ keyword, val_ "%"])
                      }

beginsWith = Comparison { comparisonKind = "begins_with"
                        , comparisonParser = Aeson.withObject "begins_with" $ \v -> do
                                               prefix <- v .: "begins_with"
                                               pure (FieldFilter $
                                                    \e -> sqlBool_ (e `like_` concat_ [val_ prefix, val_ "%"]))
                        }

endsWith = Comparison { comparisonKind = "ends_with"
                      , comparisonParser = Aeson.withObject "ends_with" $ \v -> do
                                             suffix <- v .: "ends_with"
                                             pure (FieldFilter $ \e -> sqlBool_ (e `like_` concat_ [val_ "%", val_ suffix]))
                      }

isEqualTo :: (HasSqlEqualityCheck Postgres a, Aeson.FromJSON a, BeamSqlBackendCanSerialize Postgres a)
           => Comparison a
isEqualTo = Comparison { comparisonKind = "is_equal"
                       , comparisonParser = Aeson.withObject "is_equal" $ \v -> do
                                              a <- v .: "is_equal"
                                              pure (FieldFilter $ \e -> e ==?. val_ a)
                       }

meetsCriteria :: forall tbl db
               . SingleFieldPrimaryKey tbl
              => (forall s. Q Postgres db s (QExprTable Postgres s tbl))
              -> [ QueryField db tbl ] -> Comparison (SingleFieldType tbl)
meetsCriteria tbl fields =
    Comparison { comparisonKind = "meets_criteria"
               , comparisonParser = \x -> do
                   s <- queryParser fields x
                   case s of
                     NoSearch -> pure NoFieldFilter
                     Search s ->
                         pure (FieldFilter $ \e ->
                                   sqlBool_ $ exists_ $ do
                                     t <- tbl
                                     guard_' (s t)
                                     pure (as_ @Int32 $ val_ 1))
               }

isBefore, isAfter, isBetween :: (Aeson.FromJSON a, BeamSqlBackendCanSerialize Postgres a)
                             => Comparison a
isBefore = Comparison { comparisonKind = "is_before"
                      , comparisonParser = Aeson.withObject "is_before" $ \v -> do
                                             a <- v .: "is_before"
                                             pure (FieldFilter $ \e -> sqlBool_ $ e <. val_ a)
                      }
isAfter = Comparison { comparisonKind = "is_after"
                     , comparisonParser = Aeson.withObject "is_after" $ \v -> do
                                            a <- v .: "is_after"
                                            pure (FieldFilter $ \e -> sqlBool_ $ e >. val_ a)
                     }

isBetween = Comparison { comparisonKind = "is_between"
                       , comparisonParser = Aeson.withObject "is_between" $ \v -> do
                                              after <- v .: "min"
                                              before <- v .: "max"
                                              pure (FieldFilter $ \e -> sqlBool_ $
                                                                        e >=. val_ after &&.
                                                                        e <=. val_ before)
                       }
