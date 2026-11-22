/*
  Local derivations for lean-temper's gate tools (D9, docs/plans/nix-images.md:
  a version change is a local definition, never a nixpkgs-wide overlay, so no
  unrelated package rebuilds).

  mkLean builds one Lean release as a patched upstream tarball (D11: no elan,
  no toolchain download at run time). lean435's version and fetched hash are
  the same upstream tarball exophial's own nix/gate.nix lean4350 pins; copying
  the hash is a reuse of a content hash already verified there, not a trust
  decision -- lean-temper does not import exophial's flake.
*/
{ pkgs }:
let
  mkLean =
    version: hash:
    pkgs.stdenv.mkDerivation {
      pname = "lean4";
      inherit version;
      src = pkgs.fetchurl {
        url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.tar.zst";
        inherit hash;
      };
      nativeBuildInputs = [
        pkgs.autoPatchelfHook
        pkgs.zstd
      ];
      buildInputs = [
        pkgs.stdenv.cc.cc.lib
        pkgs.gmp
        pkgs.libuv
        pkgs.zlib
      ];
      unpackCmd = ''
        zstd -d --stdout "$curSrc" | tar -x
      '';
      installPhase = ''
        runHook preInstall
        mkdir -p $out
        cp -r --no-preserve=ownership . $out/
        chmod -R u+w $out
        find $out/bin -maxdepth 1 -type f -exec chmod +x {} +
        runHook postInstall
      '';
    };
in
{
  inherit mkLean;
  # lean-temper's own lean-toolchain names exactly this version: the gate
  # carries one toolchain, with no version-dispatch shim (contrast
  # exophial's own gate, which carries two and needs one).
  lean435 = mkLean "4.35.0" "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";
}
