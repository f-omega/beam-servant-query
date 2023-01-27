{pkgs, ...}: {
  name = "beam-servant-query";
  index-state = "2023-01-26T00:00:00Z";
  compiler-nix-name = "ghc944"; # Version of GHC to use

  crossPlatforms = p: [];

  #p: pkgs.lib.optionals pkgs.stdenv.hostPlatform.isx86_64 ([
  #  p.mingwW64
  #  p.ghcjs
  #] ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [
  #  p.musl64
  #]);

  # Tools to include in the development shell
  shell.tools.cabal = "latest";
  # shell.tools.hlint = "latest";
  # shell.tools.haskell-language-server = "latest";
}
