{
  description = "A simple & fast Nix type system implemented in Nix";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = {nixpkgs, ...}: (
    let
      inherit (nixpkgs) lib;
    in {
      lib = import ./default.nix {inherit lib;};
    }
  );
}
