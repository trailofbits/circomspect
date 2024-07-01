{
  description = "A devShell example";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  inputs.flake-compat.url = "github:edolstra/flake-compat";
  inputs.flake-compat.flake = false;

  inputs.rust-overlay.url = "github:oxalica/rust-overlay";

  outputs = { self, nixpkgs, flake-utils, flake-compat, rust-overlay,
	      ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };
        stableToolchain = pkgs.rust-bin.stable."1.66.0".minimal.override {
          extensions = [ "rustfmt" "clippy" ];
        };
      in with pkgs;
      {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs;
            [
              stableToolchain
            ];

          RUST_BACKTRACE = 1;
          RUST_LOG = "info";
        };
      }
  );


}
