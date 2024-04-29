let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let deepsea = ( pkgs.fetchFromGitHub {
    owner  = "Coda-Coda";
    repo   = "deepsea-1";
    rev    = "acfba798693af79e41f25102a88ad364cfa80578";
    sha256 = "0435zmmcchvd4mpa1mpdpci5p4wnbnkvjl2v78py4igsgqxsdzjw"; } );
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