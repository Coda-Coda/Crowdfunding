# A Crowdfunding Smart Contract and Correctness Proof

This branch is used for building slides for [a talk at the Ethereum Engineering Group Meetup](https://github.com/Coda-Coda/Alectryon-slides/tree/eth-eng-grp-talk-2023) making use of [Alectryon](https://github.com/cpitclaudel/alectryon).

## Using this repository - Please read this

Please be aware that the MIT licence only applies to the source code of the files within this repository. It **does not apply to the DeepSEA codebase** (the DeepSEA codebase is essential for most potential uses of this repository). As a result, for practical purposes, _you are likely to only be able to use this repository for educational, research or evaluation purposes, and not for commercial use_, due to the limitations of the CompCert Licence.

Please see that licence here:
  https://github.com/Coda-Coda/deepsea-1/blob/main/CompCert-LICENSE.txt

The valued work of the INRIA CompCert research project (see 
https://github.com/AbsInt/CompCert) and the further work by CertiK 
building upon it made available at https://github.com/ShentuChain/DeepSEA is
all greatly appreciated.

## Instructions for getting started:

1. Get [Nix](https://nixos.org/download.html).

2. Run the following:
```
nix-build
nix-shell
compile-coq demo
```

3. Open `proofs/FunctionalCorrectness.v` in your favourite Coq IDE and begin proving! 🐔