{
  description = "lean-temper: Nix-built commit-boundary gate image (docs/plans/nix-images.md Milestone 3, T3.x.b)";

  inputs = {
    # Pinned to the shared rev every Nix-images-migration repo on this host
    # uses (operator ruling 2026-11-21): a store path is shared instead of
    # rebuilding a second copy of the toolchain.
    nixpkgs.url = "github:NixOS/nixpkgs/ac62194c3917d5f474c1a844b6fd6da2db95077d";

    # Its own nixpkgs pin, not `follows`, same as exophial's own flake.nix: it
    # builds only the nix2container tool and skopeo, never the image's
    # contents.
    nix2container.url = "github:nlewo/nix2container/42d1df94f001a9416ef08be7b305144074aca9d2";
  };

  outputs =
    {
      nixpkgs,
      nix2container,
      ...
    }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      lib = pkgs.lib;
      n2c = nix2container.packages.${system}.nix2container;
      # lib.cleanSource: VCS cruft only (.git etc). The actual commit-boundary
      # gate run hands this flake an already-filtered, .git-free judged-tree
      # tar (gate_container._extract_context_tar), never this live worktree --
      # this path only matters for a direct `nix build` against a checkout.
      gateSrc = pkgs.lib.cleanSource ./.;

      pins = import ./nix/pins.nix { inherit pkgs; };
      exophialGate = import ./nix/gate.nix {
        inherit
          pkgs
          lib
          n2c
          pins
          gateSrc
          ;
      };
    in
    {
      packages.${system} = {
        exophial-gate = exophialGate;
      };
    };
}
