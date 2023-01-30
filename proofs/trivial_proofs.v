Require Import trivial.DataTypeOps.
Require Import trivial.LayerCONTRACT.

Require Import DeepSpec.lib.Monad.StateMonadOption.
Require Import DeepSpec.lib.Monad.RunStateTInv.
Require Import lib.ArithInv.
Import DeepSpec.lib.Monad.Monad.MonadNotation.

Require Import Lia.
Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import cclib.Maps.
Require Import cclib.Integers.

Require Import DataTypes.
Require Import backend.MachineModel.

Require Import DataTypes.
Import ListNotations.

Require Import core.MemoryModel. 
Require Import HyperTypeInst.

Require Import Maps.
Import Maps.Int256Tree_Properties.
Import Maps.Int256Tree.

Require Import trivial.ContractModel.
Import trivial.ContractModel.ContractModel.

Open Scope Z.

Section Proof.

Context (contract_address : addr).
Context {memModelOps : MemoryModelOps mem}.

Lemma trivial_example : forall context before result after,
  runStateT (Trivial_boolToInt_opt true (make_machine_env contract_address before context (fun _ _ _ _ => true))) (contract_state before)
= Some (result, after)
-> result = 1.
Proof.
  intros.
  Transparent Trivial_boolToInt_opt. unfold Trivial_boolToInt_opt in H.
  inv_runStateT_branching.
  auto.
Qed.

Print Trivial_boolToInt_opt.


Lemma trivial_example2 : forall input context before result after,
  let machine_environment := (make_machine_env contract_address before context (fun _ _ _ _ => true)) in
  runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
= Some (result, after)
-> result = 1 <-> input = true.
Proof.
  intros. (* .all -.h#machine_environment -.h#memModelOps *)
  Transparent Trivial_boolToInt_opt. (* .-  *) unfold Trivial_boolToInt_opt in H. (* .in *)
  split; intros.
    - inv_runStateT_branching; subst.
      + auto.
      + discriminate.
    - inv_runStateT_branching; subst.
      + auto.
      + discriminate.
  Qed.


Lemma trivial_example2_short : forall input context before result after,
  runStateT (Trivial_boolToInt_opt input (make_machine_env contract_address before context (fun _ _ _ _ => true))) (contract_state before)
= Some (result, after)
-> result = 1 <-> input = true.
Proof.
  intros.
  Transparent Trivial_boolToInt_opt. unfold Trivial_boolToInt_opt in H.
  split; intros; inv_runStateT_branching; subst; try auto; try discriminate.
Qed.
