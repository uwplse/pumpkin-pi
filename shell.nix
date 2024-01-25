let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-23.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
in


pkgs.mkShell {
  packages = with pkgs; [
    vim
    gitFull
    openssh
    coq_8_9
    gnumake
    diff-so-fancy # specific to me
  ];
}

