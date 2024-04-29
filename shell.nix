let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let deepsea = ( pkgs.fetchFromGitHub {
    owner  = "Coda-Coda";
    repo   = "deepsea-1";
    rev    = "cd2754bc8e6cbee26bcbf77844fdaddd6705f34a";
    sha256 = "10cg8bf4zdc3zn56p8wib8c0yivkibpcl1dr89j8934n0y9rl6vy"; } );
    # To update the sha256 run:
    # nix-prefetch-url --unpack https://github.com/Coda-Coda/deepsea-1/archive/commitHashGoesHere.tar.gz
    # Then replace sha256 = ... with the last string of characters returned by nix-prefetch-url
in

let dependencies = import (deepsea + "/dependencies.nix"); in

pkgs.mkShell {
  name = "DeepSEA-env";
  buildInputs = [
    dependencies.other
    dependencies.proving
    dependencies.dsc
  ];

  shellHook = ''
    export PATH=$PATH:$PWD/result/scripts/
  '';
}