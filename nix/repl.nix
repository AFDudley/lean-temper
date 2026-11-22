/*
  The Lean REPL (https://github.com/leanprover-community/repl), built at
  v4.35.0. lean-temper's own README names it as the tool its `--repl` flag
  wants, "built at the target's toolchain" -- this repository's own
  lean-toolchain, v4.35.0. The repl's own lake-manifest.json carries no
  dependency (`"packages": []`), so this build fetches nothing beyond the
  source itself: no fixed-output derivation is needed here.
*/
{ pkgs, lean435 }:
let
  src = pkgs.fetchFromGitHub {
    owner = "leanprover-community";
    repo = "repl";
    rev = "58bdde1ff173117960083cc5a052a11d51c49ff1"; # tag v4.35.0
    hash = "sha256-HsP8w4V0FC5r46axS6WAjmzLBgQUvoPNZHNY/bIWF+k=";
  };
in
pkgs.stdenv.mkDerivation {
  pname = "lean-repl";
  version = "4.35.0";
  inherit src;
  dontFixup = true;
  buildPhase = ''
    export HOME=$TMPDIR
    export PATH=${lean435}/bin:$PATH
    lake build
  '';
  installPhase = ''
    mkdir -p $out
    cp -r . $out/
  '';
}
