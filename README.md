# A Crowdfunding Smart Contract and Correctness Proof

Making use of the DeepSEA system, this repository demonstrates proving the three properties important to the correctness of a crowdfunding smart contract.

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
./compile-coq Crowdfunding         # Note: do not include ".ds"
```

3. Open `proofs/FunctionalCorrectness.v` in your favourite Coq IDE (v. 8.14.1) and explore the proofs! 🐔

E.g.
```
nix-shell
coqide ./proofs/FunctionalCorrectness.v
```