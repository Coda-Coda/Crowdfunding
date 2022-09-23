# A Crowdfunding Smart Contract and Correctness Proof

## Sections of note relating to the SPLASH 2022 poster
 - [proofs/FunctionalCorrectness.v line 182](https://github.com/Coda-Coda/Crowdfunding/blob/splash-2022-poster/proofs/FunctionalCorrectness.v#L182) has the definition of the type `Action` which is a critical definition for the successful calls only approach. Note in particular the required arguments such as `case_donate_prf` which are the proofs required to be passed in that the call will succeed.
 - [proofs/FunctionalCorrectness.v line 399](https://github.com/Coda-Coda/Crowdfunding/blob/splash-2022-poster/proofs/FunctionalCorrectness.v#L399) has the proof of the `donation_preserved` lemma making use of the successful calls only approach.
 - [proofs/FunctionalCorrectness.v line 525](https://github.com/Coda-Coda/Crowdfunding/blob/splash-2022-poster/proofs/FunctionalCorrectness.v#L525) has the statement of the lemma `sufficient_funds_safe` described on the poster. The proof has been completed using a similar model (making use of the snapshot approach but not the successful-calls-only approach) and is available [at this link](https://github.com/Coda-Coda/deepsea-1/blob/splash-2022-poster/contracts/crowdfunding/FunctionalCorrectness.v#L688).


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