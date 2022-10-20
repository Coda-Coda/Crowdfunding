# A Crowdfunding Smart Contract and Correctness Proof

Making use of the DeepSEA system, this repository demonstrates proving the correctness of a crowdfunding smart contract. This is a **work in progress**.

This branch focuses on an approach where model is set up to only allow successful calls, except the one `revert` case which models all failures - which cause a revert.

## Sections of note relating to the FTSCS 2022 Paper
 - Listing 1: Statement of the _donation preserved_ lemma
   - [`since_as_long`, `donation_recorded`, `no_claims_from`](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L353)
   - [`donation_preserved`](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L482).
- [Listing 2: Section variables for the model](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L72)
- [Listing 3: Example of an assumption](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L95)
- [Listing 4: Initial state of the model](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L80)
- [Listing 5: Action dependent on the current blockchain state](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L183)
- [Listing 6: Step function](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L213)
- [Listing 7: `donation_preserved` proof](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L482)
- [Listing 8: Simplified proof situation at the first bullet of `donation_preserved`](https://github.com/Coda-Coda/Crowdfunding/blob/FTSCS-2022/proofs/FunctionalCorrectness.v#L499)
  - To view the proof state follow the instructions outlined in _"Instructions for getting started"_ below. In CoqIDE you could navigate to line 499 then click _"Go to cursor"_ or via the menu: "Navigation" > "Go to".

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
./compile-coq Crowdfunding
```
`nix-build` and `nix-shell` may take some time the first time they are run as they are installing the necessary dependencies and building DeepSEA.

3. Open `proofs/FunctionalCorrectness.v` in your favourite Coq IDE and begin proving! 🐔

E.g.
```
nix-shell
coqide proofs/FunctionalCorrectness.v
```