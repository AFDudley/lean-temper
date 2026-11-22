/*
  lean-temper's commit-boundary gate image, built by Nix with nix2container
  (docs/plans/nix-images.md T3.x.b; D1-D11). Ports .exophial/gate/Dockerfile
  instruction for instruction:

    toolsLayer   bashInteractive, coreutils, and the pinned Lean v4.35.0
                 toolchain (lean, lake, leanc, lean4checker) -- no elan (D11):
                 lean-temper's own lean-toolchain names exactly this version
    fhsLayer     /usr/bin/env: .exophial/gate/gate.sh's own `#!/usr/bin/env
                 bash` shebang (measured: with no /usr/bin/env, `exec
                 .exophial/gate/gate.sh` reports "no such file or
                 directory" -- the missing path is the interpreter, not the
                 script itself)
    per commit   the judged tree, placed at /gate

  .exophial/gate/gate.sh runs only `lake build` then `lake build tests`.
  lean-temper's own lake-manifest.json carries no dependency (packages: []),
  so this build fetches nothing: no Mathlib cache, no fixed-output
  derivation, is needed for this image.

  `copyToPodman` copies only the layers podman does not already hold.
*/
{
  pkgs,
  lib,
  n2c,
  pins,
  gateSrc,
}:
let
  toolPaths = [
    (pkgs.dockerTools.fakeNss.override { extraGroupLines = [ "nogroup:x:65534:" ]; })
    pkgs.bashInteractive
    pkgs.coreutils
    pkgs.gnugrep
    pkgs.gnused
    pkgs.findutils
    pkgs.which
    pins.lean435
  ];

  toolsEnv = pkgs.buildEnv {
    name = "lean-temper-gate-tools";
    paths = toolPaths;
    ignoreCollisions = true;
  };
  toolsLayer = n2c.buildLayer { copyToRoot = [ toolsEnv ]; };

  fhsRoot = pkgs.runCommand "lean-temper-gate-fhs-root" { } ''
    mkdir -p $out/usr/bin
    ln -s ${pkgs.coreutils}/bin/env $out/usr/bin/env
  '';
  fhsLayer = n2c.buildLayer {
    copyToRoot = [ fhsRoot ];
    layers = [ toolsLayer ];
  };

  # The judged tree, placed AT /gate: `copyToRoot` merges a listed path's own
  # CONTENTS at the image root, so `gateSrc` itself (a plain checkout
  # directory) would land its files at `/`, not `/gate` -- this wrapper puts
  # them at `/gate` (the same step exophial's own gate-image build performs
  # for its gateTree).
  gateTree = pkgs.runCommand "lean-temper-gate-tree" { } ''
    mkdir -p $out/gate
    cp -r ${gateSrc}/. $out/gate/
  '';
in
n2c.buildImage {
  # Fully qualified: containers-storage stores a short name as
  # docker.io/library/<name>, and a short name lets podman resolve it against
  # a remote registry. A localhost/ name never resolves there.
  name = "localhost/lean-temper-gate";
  layers = [
    toolsLayer
    fhsLayer
  ];
  copyToRoot = [ gateTree ];
  config = {
    WorkingDir = "/gate";
    # No Entrypoint: the gate passes gate.command (.exophial/gate/gate.sh)
    # directly, in WORKDIR /gate with this PATH -- the same contract
    # .exophial/gate/Dockerfile's own final comment states.
    Env = [
      "PATH=/bin"
      "HOME=/root"
    ];
  };
}
