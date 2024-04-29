let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let deepsea = ( pkgs.fetchFromGitHub {
    owner  = "Coda-Coda";
    repo   = "deepsea-1";
    rev    = "02267424eb5e8f4c03bcb88a4bd2a2e4643eddbd";
    sha256 = "0bg7yffp6lal3zmxqfn2068s9d8ljlslp385na9fgjbn2lmjsy9q"; } );
    # To update the sha256 run:
    # nix-prefetch-url --unpack https://github.com/Coda-Coda/deepsea-1/archive/commitHashGoesHere.tar.gz
    # Then replace sha256 = ... with the last string of characters returned by nix-prefetch-url
in

let dependencies = import (deepsea + "/dependencies.nix"); in

pkgs.stdenv.mkDerivation {
  name = "dsc-and-deepsea-coq-built";
  
  buildInputs = [
    dependencies.other
    dependencies.proving
    dependencies.dsc
    dependencies.documentation
  ];

  src = deepsea;

  patches = [ (deepsea + /patches/DeepSpec-in-result.patch) ];

  postPatch = ''
    patchShebangs .
  '';

  buildPhase = ''
    make --always-make
    make --always-make parser
    make --always-make edsger
    
    # Build documentation
    make coqdoc
    mkdocs build -d docs-site
  '';

  installPhase = ''
    mkdir -p $out

    echo "=========================================="
    echo "The files being built are from https://github.com/Coda-Coda/deepsea-1 which is a fork of https://github.com/ShentuChain/deepsea which is based on the INRIA CompCert Research project: https://github.com/AbsInt/CompCert"
    echo "These files may only be used for educational, research or evaluation purposes, and not for commercial use. For the actual licence, please see the CompCert-LICENCE.txt file which is included with the built files."
    echo "These files are NOT licensed the same as the repository holding this file with these messages (default.nix)."
    echo "=========================================="

    cp -r . $out

  '';
}