{
  description = "Silean 2 Lean, FIRRTL, and simulation development environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      forEachSystem = nixpkgs.lib.genAttrs supportedSystems;
    in {
      devShells = forEachSystem (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          python = pkgs.python312.withPackages (packages: with packages; [
            cocotb
            pytest
          ]);
        in {
          default = pkgs.mkShell {
            packages = with pkgs; [
              circt
              elan
              gnumake
              python
              verilator
            ];

            shellHook = ''
              export PS1="\[\e[1;35m\][silean2]\[\e[0m\] $PS1"
            '';
          };
        });
    };
}
