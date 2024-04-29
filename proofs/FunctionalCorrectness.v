Require Import Crowdfunding.DataTypeOps.
Require Import Crowdfunding.LayerCONTRACT.

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

Require Import Crowdfunding.DataTypes.
Require Import backend.MachineModel.

Import ListNotations.

Require Import core.MemoryModel. 
Require Import HyperTypeInst.

Require Import Maps.
Import Maps.Int256Tree_Properties.
Import Maps.Int256Tree.

Require Import Crowdfunding.ContractModel.
Import Crowdfunding.ContractModel.ContractModel.

Open Scope Z.

Delimit Scope int256_scope with int256.
Infix "+" := Int256.add : int256_scope.
Infix "-" := Int256.sub : int256_scope.
Infix "=?" := Int256.eq (at level 70, no associativity) : int256_scope.

Ltac me_transfer_cases :=
  try match goal with
    H : (Int256.one =? Int256.one)%int256 = false |- _ => 
      rewrite Int256.eq_true in H; discriminate
      end;
  try match goal with
    H : runStateT mzero _ = ret _ |- _ => 
    simpl in H; discriminate
  end.

Ltac ds_inv :=
      repeat (
        try inv_runStateT_branching;
        let Case := fresh "NoOverflowOrUnderflowInTransferCase" in
        try match goal with
          | H : context[me_transfer _  _ _] |- _ => 
          unfold me_transfer, make_machine_env in H;
          destruct (noOverflowOrUnderflowInTransfer _ _ _ _
                    && (_ _ _ _ _)) eqn:Case
        end
      );
      me_transfer_cases.

Section GenericProofs.
Lemma fold_snd_map : 
  forall  A B (m : list (A * B)) x f,
  (fold_left (fun (a : B) (p : A * B) => f a (snd p))
   m x) = 
  (fold_left f
  (List.map snd m) x).
Proof.
    intro.
    induction m.
    - intros. simpl. reflexivity.
    - intros. simpl. rewrite IHm. reflexivity.
Qed. 


Lemma sum_starting_from_init_equals_sum_plus_init_arbitrary_start : 
forall (x init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m (init + x) = Z.add (Int256Tree.fold1 Z.add m x) init.
Proof.
  intros.
  repeat rewrite Int256Tree.fold1_spec.
  assert(
  forall x,
    (fold_left (fun (a : Z) (p : Int256Tree.elt * Z) => Z.add a (snd p))
    (Int256Tree.elements m) x) = 
    (fold_left Z.add
    (List.map snd (Int256Tree.elements m)) x)).
    {
      intros.
      apply fold_snd_map.
    }
  repeat rewrite H. clear H.
  rewrite <- fold_left_last.
  repeat rewrite fold_symmetric; try (intros; lia).
  remember (List.map snd (Int256Tree.elements m)) as l.
  clear Heql. clear m. generalize dependent l.
  induction l.
    - simpl. lia.
    - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Lemma sum_starting_from_init_equals_sum_plus_init : 
forall (init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m init = Z.add (Int256Tree.fold1 Z.add m 0) init.
Proof.
  intros.
  rewrite <- sum_starting_from_init_equals_sum_plus_init_arbitrary_start.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma Int256Tree_sum_set_value_initially_zero : 
  forall (m: Int256Tree.t Z32)  k v, Int256Tree.get_default 0 k m = 0
                -> Int256Tree_Properties.sum (Int256Tree.set k v m) = 
                   Int256Tree_Properties.sum m + v.
Proof.
  unfold Z32.
  intros.
  pose (@Int256Tree_Properties.sum_get_default 0 k v (Int256Tree.set k v m)) as Lemma1.
  simpl in Lemma1.
  unfold Int256Tree_Properties.sum.
  rewrite Lemma1; [|  unfold Int256Tree.get_default;
                      rewrite Int256Tree.gss;
                      reflexivity].
  rewrite Int256Tree_Properties.fold1_remove_set; [|intros; lia].
  unfold Int256Tree.get_default in H.

  destruct (Int256Tree.get k m) eqn:Case.
  - rewrite H in Case.
     assert(Zswap : forall x y a : Z, a + x + y = a + y + x) by (intros; lia).
     epose (Int256Tree_Properties.fold1_get Z.add Zswap v Case) as H0.
     rewrite Z.add_0_r in H0.
     rewrite <- H0.
     pose Int256Tree_Properties.sum_extensional.
     apply sum_starting_from_init_equals_sum_plus_init.
   - 
   assert(Int256Tree.get_default 0 k m = 0).
   unfold Int256Tree.get_default.
   rewrite Case. reflexivity. 
   pose (@Int256Tree_Properties.sum_get_default v k 0 m H0).
   rewrite Z.add_0_r in e.
   rewrite <- e.
   apply sum_starting_from_init_equals_sum_plus_init.
Qed.

Lemma sum_set_y_remove_from_starting_x : 
  forall k m x y,
  Int256Tree.fold1 Z.add (Int256Tree.set k y m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x + y.
Proof.
  intros.
  pose (Int256Tree.grs k m).
  pose (Int256Tree_Properties.set_permutation 0 e).
  rewrite <- Int256Tree_Properties.elements_set_decompose in p.
  rewrite fold1_set by lia.
  rewrite sum_starting_from_init_equals_sum_plus_init.
  symmetry.
  rewrite sum_starting_from_init_equals_sum_plus_init.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Lemma sum_set_zero_remove_from_starting_x : 
  forall k m x,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x.
Proof.
  intros.
  rewrite sum_set_y_remove_from_starting_x.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma sum_set_zero_remove : 
  forall k m,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) 0 =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) 0.
Proof.
  intros.
  apply sum_set_zero_remove_from_starting_x.
Qed.

Lemma sum_set_x_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v x init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k x m) init = fold1 Z.add m init + (x - v).
Proof.
unfold sum.
  intros.
  unfold Int256Tree_Properties.sum.
  unfold Int256Tree.get_default in H.
  destruct (Int256Tree.get k m) eqn:Case.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      epose (Int256Tree_Properties.fold1_get Z.add H init Case).
      rewrite e.
      simpl.
      assert (init + v = v + init) by apply Z.add_comm.
      rewrite H0. clear H0.
      rewrite (sum_starting_from_init_equals_sum_plus_init_arbitrary_start init).
      rewrite sum_set_y_remove_from_starting_x.
      lia.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      simpl.
      rewrite Z.sub_0_r.
      rewrite sum_set_y_remove_from_starting_x.
      assert(get_default 0 k m = 0). unfold get_default. rewrite Case. reflexivity.
      pose proof (@sum_get_default init k 0 m H0).
      rewrite Z.add_0_r in H1.
      rewrite <- H1.
      reflexivity.
Qed.

Lemma sum_set_zero_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k 0 m) init = fold1 Z.add m init - v
.
Proof.
intros.
apply sum_set_x_minus_from_arbitrary_init; assumption.
Qed.

Lemma sum_set_zero_minus : forall k m v, Int256Tree.get_default 0 k m = v ->
Int256Tree_Properties.sum (Int256Tree.set k 0 m) = Int256Tree_Properties.sum m - v.
Proof.
  intros.
  unfold sum.
  apply sum_set_zero_minus_from_arbitrary_init.
  assumption.
Qed.

Lemma Int256Tree_sum_minus_equality : 
  forall m k x,
    Int256Tree_Properties.sum m >= x
    ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m) =
    (Int256Tree_Properties.sum m) - (Int256Tree.get_default 0 k m).
Proof.
intros.
unfold sum.
rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
reflexivity.
Qed.

Lemma Int256Tree_sum_minus_from_starting_x :
  forall (m : t Z) (k : elt) (x : Z),
      fold1 Z.add (set k 0 m) x =
      fold1 Z.add m x - get_default 0 k m.
Proof.
  intros.
  rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
  reflexivity.
Qed.

Lemma Int256Tree_sum_minus : 
  forall m k x,
    Int256Tree_Properties.sum m <= x
    ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m) <=
    x - (Int256Tree.get_default 0 k m).
Proof.
intros.
rewrite sum_set_zero_minus with (v:= Int256Tree.get_default 0 k m) by reflexivity.
lia.
Qed.

End GenericProofs.

Module FunctionalCorrectness.

Section Blockchain_Model.

Open Scope int256.

Context
  (snapshot_timestamp : int256)
  (snapshot_number : int256)
  (snapshot_blockhash : int256 -> int256)
  (snapshot_balances : addr -> wei).

Context
  (snapshot_balances_valid_prf : forall a, 0 <= (snapshot_balances a) < Int256.modulus).

Context
  (contract_address : addr).

Definition ContractState := global_abstract_data_type.

Context
  (address_accepts_funds : option ContractState -> addr -> addr -> wei -> bool).
(* The following is a helpful alternative to suppose instead of using `address_accepts_funds` alone. But it must be assumed explicitly. *)
Definition address_accepts_funds_assumed_for_from_contract 
  d sender recipient amount :=
  if sender =? contract_address then true else
  address_accepts_funds d sender recipient amount.
Close Scope int256.
Definition address_accepts_funds_assumption (_ : option ContractState) (_ _ : addr) (_ : wei) := true.
(* The current model also has the implicit assumption that the transfers to a smart contract during a function call via callvalue are always accepted by the contract.
   This could be changed by editing callvalue_prf in the definition of Action, similarly to how it is done for `externalBalanceTransfer` *)

Definition constructor_call_context :=
  {| origin := Int256.zero;
     caller := Int256.zero;
     callvalue := 0;
     coinbase := Int256.zero;
     chainid := Int256.zero |}.

Definition constructor_blockchain_state :=
  {| timestamp := snapshot_timestamp;
    block_number := snapshot_number;
    balance := snapshot_balances;
    blockhash := snapshot_blockhash;
    contract_state := init_global_abstract_data |}.

Program Definition constructor_machine_env := make_machine_env contract_address constructor_blockchain_state constructor_call_context address_accepts_funds_assumption _ _ _.
Next Obligation.
unfold Int256.modulus, two_power_nat. lia.
Defined.
Next Obligation.
unfold noOverflowOrUnderflowInTransfer.
rewrite Z.add_0_r. rewrite Z.sub_0_r.
rewrite andb_true_iff.
split.
pose proof (snapshot_balances_valid_prf Int256.zero). lia.
pose proof (snapshot_balances_valid_prf contract_address). lia.
Defined.

Context {HmemOps: MemoryModelOps mem}.
Context {memModelOps : MemoryModelOps mem}.

(** * Initial State *)

Definition init_state :=
  match runStateT (Crowdfunding_constructor_opt constructor_machine_env) init_global_abstract_data
  with
  | Some (_, d) => Some d
  | None => None
  end.

Lemma same_init : init_state = Some init_global_abstract_data.
Proof.
  unfold init_state.
  vm_compute.
  unfold init_global_abstract_data.
  reflexivity.
Qed.

Print init_global_abstract_data.

Definition initial_state :=
  mkBlockchainState
    snapshot_timestamp
    snapshot_number
    snapshot_balances
    snapshot_blockhash
    init_global_abstract_data.

Definition updateTimeAndBlock before block_count time_passing : BlockchainState :=
mkBlockchainState
  (time_passing + (timestamp before))%int256
  (block_count + (block_number before))%int256
  (balance before)
  (blockhash before)
  (contract_state before).

Definition validTimeChange block_count time_passing current_block_number current_timestamp : bool :=
  (* Note, testing for positive block_count and time_passing is unnecessary while they are Int256 values.
     It would be necessary to add positivity checks if using Z instead of course. *)
  ((Int256.intval block_count) + (Int256.intval current_block_number) <=? Int256.max_unsigned)%Z
  && ((Int256.intval time_passing) + (Int256.intval current_timestamp) <=? Int256.max_unsigned)%Z.

Definition update_balances sender recipient amount balances : (addr -> wei) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => 
  if (sender =? recipient)%int256 then balances a else
    if (a =? sender)%int256 then (balances sender) - amount else
     if (a =? recipient)%int256 then (balances recipient) + amount
      else balances a.

Definition update_balance before latest_balances : BlockchainState :=
  mkBlockchainState
  (timestamp before)
  (block_number before)
  latest_balances
  (blockhash before)
  (contract_state before)
.


Definition current_balances 
  (* Note on where insufficient balance-checking takes place:
     Overflow and underflow of balances must already have been checked before this function.
     (i.e. before a transfer is placed in Outgoing_transfer_recipient_and_amount it should
           have been checked to ensure no overflow/underflow.)
     Currently this check is expected to be implemented by the me_transfer definition.
     !! Ensure you are using an appropriate me_transfer definition. !! *)
  (successful_transfer : option (addr * Z))
  (initial_balances : addr -> wei) 
  : (addr -> wei) :=
    match successful_transfer with
      | None => initial_balances
      | Some (recipient, amount) => 
          update_balances contract_address recipient amount initial_balances
    end.

Definition new_balance_after_contract_call (before : BlockchainState) (context : CallContext) (d : ContractState) : (addr -> wei) :=
    (current_balances
      (Outgoing_transfer_recipient_and_amount d)
      (update_balances (caller context) contract_address (callvalue context) (balance before))).

Definition resetTransfers (d : ContractState) : ContractState :=
  {|
  Crowdfunding_owner := Crowdfunding_owner d;
  Crowdfunding_max_block := Crowdfunding_max_block d;
  Crowdfunding_goal := Crowdfunding_goal d;
  Crowdfunding_backers := Crowdfunding_backers d;
  Crowdfunding_funded := Crowdfunding_funded d;
  Outgoing_transfer_recipient_and_amount := None
|}.

Definition next_blockchain_state (before : BlockchainState) (context : CallContext) (contract_state_after : ContractState) : BlockchainState :=
  mkBlockchainState
    (timestamp before)
    (block_number before)
    (new_balance_after_contract_call before context contract_state_after)
    (blockhash before)
    (resetTransfers contract_state_after).

Definition next_blockchain_state_keep_transfer (before : BlockchainState) (context : CallContext) (d : ContractState) : BlockchainState :=
  mkBlockchainState
    (timestamp before)
    (block_number before)
    (new_balance_after_contract_call before context d)
    (blockhash before)
    d.

(* This approach to defining Action requires all calls to a contract
   function to succeed, i.e. return (Some _ _), failure cases are
   amalgamated into the revert case. This means only needing to prove
   the (typically) trivial revert case once, without losing generality. *)
Inductive Action (before : BlockchainState) :=
  | call_Crowdfunding_donate (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling donate successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling donate successfully given the context (and arguments, if applicable) *)
      (case_donate_prf : 
          runStateT (Crowdfunding_donate_opt (make_machine_env contract_address before context address_accepts_funds_assumption callvalue_bounded_prf balances_bounded_prf callvalue_prf)) (contract_state before)
          = Some (r, contract_state_after))
  | call_Crowdfunding_getFunds (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling getFunds successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling getFunds successfully given the context (and arguments, if applicable) *)
      (case_getFunds_prf : 
          runStateT (Crowdfunding_getFunds_opt (make_machine_env contract_address before context address_accepts_funds_assumption callvalue_bounded_prf balances_bounded_prf callvalue_prf)) (contract_state before)
          = Some (r, contract_state_after))
  | call_Crowdfunding_claim (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling claim successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling claim successfully given the context (and arguments, if applicable) *)
      (case_claim_prf : 
          runStateT (Crowdfunding_claim_opt (make_machine_env contract_address before context address_accepts_funds_assumption callvalue_bounded_prf balances_bounded_prf callvalue_prf)) (contract_state before)
          = Some (r, contract_state_after))
  | externalBalanceTransfer (sender recipient : addr) (amount : wei)
      (prf : sender <> contract_address /\ amount >= 0 /\
        ((noOverflowOrUnderflowInTransfer sender recipient amount (balance before))
         && (address_accepts_funds_assumption None sender recipient amount) = true))
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (block_number before) (timestamp before) = true)
  | revert (* A no-op, or a call with some error resulting in no state change, such as a contract reverting during its code execution, or such as calling an invalid function when there is no fallback defined. *).

(** * Step Function *)

Fixpoint step
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_Crowdfunding_donate context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state before context d_after
| call_Crowdfunding_claim context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_claim_prf => 
      next_blockchain_state before context d_after
| call_Crowdfunding_getFunds context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_getFunds_prf => 
      next_blockchain_state before context d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| revert => before
end.

Fixpoint step_keep_transfer
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_Crowdfunding_donate context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_Crowdfunding_claim context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_claim_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_Crowdfunding_getFunds context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_getFunds_prf => 
      next_blockchain_state_keep_transfer before context d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| revert => before
end.

(** * The Reachability Predicate *)

Record Step := mkStep
  {
    Step_state : BlockchainState;
    Step_action : Action Step_state
  }.

Definition stepOnce prev := (step (Step_state prev) (Step_action prev)).
Definition stepOnceAndWrap prev next_action := (mkStep (stepOnce prev) next_action).

Hint Unfold stepOnce stepOnceAndWrap.

Inductive ReachableFromBy from : BlockchainState -> Step -> list Step -> Prop :=
| initial_case
    (Hno_leftover_outgoings : Outgoing_transfer_recipient_and_amount (contract_state from) = None)
    (next_action : Action from)
    : ReachableFromBy from from (mkStep from next_action) [mkStep from next_action]
| step_case
    (prevSt : BlockchainState) (prev : Step) (prevList : list Step)
    (Hprev : ReachableFromBy from prevSt prev prevList)
    (next_action : Action (stepOnce prev))
    : ReachableFromBy from  (stepOnce prev) 
      (stepOnceAndWrap prev next_action)
      (stepOnceAndWrap prev next_action :: prevList).

Lemma ReachableFromByLinkStateToStep : forall st st' s l,
  ReachableFromBy st st' s l -> st' = Step_state s.
Proof.
  intros.
  destruct H; reflexivity.
Qed.

Lemma ReachableFromByLinkStepToList : forall st st' s l,
  ReachableFromBy st st' s l -> exists tl, s :: tl = l.
Proof.
  intros.
  destruct H.
  - exists []. reflexivity.
  - exists prevList. reflexivity.
Qed.

Ltac reachableFromByLinks := 
  match goal with
  | H : ReachableFromBy _ _ _ _ |- _ => 
    let StateToStepName := fresh "HReachableFromByLinkStateToStep" in
    let StepToListName := fresh "HReachableFromByLinkStepToList" in
    epose proof (ReachableFromByLinkStateToStep _ _ _ _ H) as StateToStepName;
    epose proof (ReachableFromByLinkStepToList _ _ _ _ H) as StepToListName
  end.

Lemma NoLeftoverOutgoings : forall {st st' s l},
  ReachableFromBy st st' s l -> Outgoing_transfer_recipient_and_amount (contract_state st') = None.
Proof.
  intros.
  induction H.
  - assumption.
  - unfold stepOnce.
    unfold step.
    destruct (Step_action prev) eqn:Case; simpl; try reflexivity.
    all: reachableFromByLinks; subst; assumption.
Qed.

(** * Preservation of Donation Record Theorem *)

Definition since_as_long (P : BlockchainState -> Prop) (Q : BlockchainState -> Prop) (R : Step -> Prop) : Prop :=
  forall (steps : list Step) (from_state to_state : BlockchainState) (to_step : Step),
    ReachableFromBy from_state to_state to_step steps ->
    P from_state ->
    (forall sa, List.In sa steps -> R sa) ->
    Q to_state.

Notation "Q `since` P `as-long-as` R" := (since_as_long P Q R) (at level 1).

Definition donation_recorded (a : addr) (amount : Z) (s : BlockchainState) : Prop :=
  Int256Tree.get_default 0 a (Crowdfunding_backers (contract_state s)) = amount /\ amount > 0.

Definition no_claims_from (a : addr) (s : Step) : Prop :=
  match Step_action s with
  | (call_Crowdfunding_claim context _ _ _ _ _ _) => a <> caller context
  | _ => True
  end.

Ltac destruct_if_H :=
  let caseName := fresh "IfCase" in
  match goal with
    | [ _ : context[if ?X then _ else _] |- _ ] => destruct X eqn:caseName
  end.

Ltac destruct_beq256_H :=
  let caseName := fresh "IfCaseBeq" in
    match goal with
      | [ _ : context[(?X =? ?Y)%int256] |- _ ] => destruct (X =? Y)%int256 eqn:caseName
    end.

Ltac destruct_geq256_H :=
  let caseName := fresh "IfCaseGeq" in
    match goal with
      | [ _ : context[(?X >=? ?Y)%int256] |- _ ] => destruct (X >=? Y)%int256 eqn:caseName
    end.

Hint Unfold Z_bounded.

Ltac destruct_and :=
  match goal with
    | [ H : (_ /\ _) |- _ ] => destruct H
  end.

Ltac Hlinks := 
  match goal with
  | H : ReachableFromBy _ _ _ _ |- _ => 
    let StateToStepName := fresh "HS" in
    let StepToListName := fresh "HL" in
    epose proof (ReachableFromByLinkStateToStep _ _ _ _ H) as StateToStepName;
    epose proof (ReachableFromByLinkStepToList _ _ _ _ H) as StepToListName
  end.

Ltac inv_FT :=
  try match goal with H : false = true |- _ => inversion H end.

Hint Unfold stepOnceAndWrap step stepOnce make_machine_env.

Definition donate_fun := Crowdfunding_donate_opt.

Open Scope int256.

Lemma addZeroBalance : forall sender recipient balances a,
  update_balances sender recipient 0 balances a = balances a.
Proof.
  intros.
  unfold update_balances.
  destruct (Int256.eq sender recipient).
  - reflexivity.
  - destruct (Int256.eq a sender) eqn:Case.
    + rewrite Z.sub_0_r.
    apply Int256eq_true in Case. subst.
    reflexivity.
    + destruct (Int256.eq a recipient) eqn:SCase.
      * rewrite Z.add_0_r.
        apply Int256eq_true in SCase. subst.
        reflexivity.
      * reflexivity.
Qed.

Theorem donation_preserved :
  forall (a : addr) (d : Z),
                 (donation_recorded a d) 
    `since`      (donation_recorded a d)
    `as-long-as` (no_claims_from a).
Proof.
unfold since_as_long.
intros. (* H H0 H1 *)
induction H.
- (* H0 *)
assumption.
- (* H H0 H1 IHReachableFromBy *)
  assert(donation_recorded a d prevSt) by (apply IHReachableFromBy;
  intros; apply H1; apply in_cons; assumption). (* H2 *)
  clear H0 IHReachableFromBy.
  unfold donation_recorded in *; destruct_and. (* H0 H2 *)
  split; [|assumption].
  Hlinks. (* HS HL *)
  assert (no_claims_from a prev) by
  (apply H1; destruct HL; subst; right; left; auto). (* H3 *)
  destruct prev; autounfold in *; simpl in *.
  clear H1 H HL.
  unfold no_claims_from in H3.
  unfold donation_recorded in *. destruct Step_action0; simpl in *;
  rewrite <- HS in *.
  + 
    Transparent Crowdfunding_donate_opt. (* case_donate_prf *)
    remember (make_machine_env contract_address Step_state0 context
                          address_accepts_funds_assumption
                          callvalue_bounded_prf balances_bounded_prf
                          callvalue_prf) as machine_environment. (* case_donate_prf *)
    unfold Crowdfunding_donate_opt in *.
    ds_inv.
    * (* H1 H4 H5 H7 H18 H20 *)
      subst. (* H20 *)
      inversion H20.
    * subst. simpl in *.
      destruct (a =? (caller context)) eqn:Case.
      -- (* Case H2 *)
         exfalso. (* Heqb0 H2 *)
         apply Int256eq_true in Case. (* Case H2 Heqb0 *)
         rewrite <- Case in *. (* Heqb0 H2 *)
         clear -H2 Heqb0.
         Check Z.eqb_eq.
         apply Z.eqb_eq in Heqb0. (* Heqb0 *)
         rewrite Heqb0 in H2. (* H2 *)
         lia.
      -- (* Case *)
        apply Int256eq_false in Case. (* Case *)
        Check get_default_so.
        apply get_default_so. (* Case *)
        apply Case.
    * subst. (* H22 *)
      reflexivity.
  + Transparent Crowdfunding_getFunds_opt.
    remember (make_machine_env contract_address Step_state0 context
                          address_accepts_funds_assumption
                          callvalue_bounded_prf balances_bounded_prf
                          callvalue_prf) as machine_environment.
    unfold Crowdfunding_getFunds_opt in *.
    Check case_getFunds_prf.
    idtac.
    rewrite Heqmachine_environment in *.
    ds_inv; subst; reflexivity.
  + (* case_claim_prf H3 *)
    Transparent Crowdfunding_claim_opt.
    unfold Crowdfunding_claim_opt in case_claim_prf.
    ds_inv; subst; simpl in *; try reflexivity.
    * (* H3 *)
      Check get_default_so.
      rewrite get_default_so by assumption.
      reflexivity.
    * (* Heqb1 *)
      apply Int256eq_true in Heqb1. (* Heqb1 *)
      discriminate.  
  + (* H0 *)
    assumption.
  + (* H0 *)
    assumption.
  + (* H0 *)
    assumption.
Qed.

Opaque Crowdfunding_donate_opt Crowdfunding_getFunds_opt Crowdfunding_claim_opt.

Close Scope int256.

(** * Safety Property of Sufficient Balance Theorem *)

Definition Safe P :=
  forall state s l, ReachableFromBy initial_state state s l -> P state.

Definition balance_backed state :=
  (Crowdfunding_funded (contract_state state)) = false
  -> 
  sum (Crowdfunding_backers (contract_state state))
    <= (balance state (contract_address)) /\
    (forall key value, get key (Crowdfunding_backers (contract_state state)) = Some value -> ((value >= 0) /\ (value < Int256.modulus))).

Print next_blockchain_state.

Lemma balance_backed_in_processed_state : 
  forall after context,
    balance_backed (Step_state after) 
    -> Outgoing_transfer_recipient_and_amount (contract_state (Step_state after))
         = None
    -> (callvalue context =? 0) = true     
    -> balance_backed
     (next_blockchain_state (Step_state after) context
     (contract_state (Step_state after))).
Proof.
 intros.
 unfold step. unfold balance_backed. simpl in *.
 unfold balance_backed in H.
 apply Z.eqb_eq in H1.
 unfold new_balance_after_contract_call. unfold current_balances. simpl.
 rewrite H1.
 intros.
 split.
 - rewrite H0.
   rewrite addZeroBalance. (* H H2 *)
   apply H. (* H2 *)
   apply H2.
 - apply H. apply H2.
Qed.

Theorem sufficient_funds_safe : Safe balance_backed.
Proof.
  unfold Safe.
  intros. (* H *)
  induction H. 
  -
    unfold initial_state, balance_backed.
    simpl.
    intros.
    unfold Int256Tree_Properties.sum.
    unfold Int256Tree.empty.
    unfold Int256Tree.fold1.
    simpl.
    split.
    +
      apply snapshot_balances_valid_prf.
    + 
      unfold Int256Tree.get_default, Int256Tree.get. 
      simpl.
      unfold PTree.empty, Int256Indexed.index.
      intros.
      destruct key.
    unfold "!".
    destruct intval; intros; discriminate.
  - Hlinks. repeat rewrite HS in *. (* IHReachableFromBy HS prev *)
    clear HS HL.
    destruct (Step_action prev) eqn:Case.
    + 
      Check case_donate_prf.
      idtac.
      Transparent Crowdfunding_donate_opt. 
      simpl in next_action.
      unfold next_blockchain_state in next_action.
      simpl in next_action.
      unfold Crowdfunding_donate_opt in case_donate_prf.
      pose proof case_donate_prf as case_donate_prf'.
      ds_inv; subst; try discriminate.
      *
        unfold stepOnce.
        unfold step.
        rewrite -> Case.
        simpl in *.
        unfold next_blockchain_state.
        unfold new_balance_after_contract_call.
        unfold current_balances.
        unfold update_balances.
        unfold update_Crowdfunding_backers.
        simpl.
        rewrite (NoLeftoverOutgoings H).
        unfold resetTransfers.
        simpl.
        unfold balance_backed.
        simpl.
        intros.
        clear Case.
        clear case_donate_prf.
        unfold balance_backed in IHReachableFromBy.
        apply IHReachableFromBy in H0.
        split.
        apply Z.eqb_eq in Heqb0.
        rewrite negb_true_iff in H2.
        rewrite H2.
        rewrite Int256.eq_true.
        rewrite Int256.eq_sym.
        rewrite H2.
        rewrite Int256Tree_sum_set_value_initially_zero; [|assumption].
        unfold noOverflowOrUnderflowInTransfer in callvalue_prf.
        destruct H0.
        simpl.
        lia.
        destruct H0.
        intros.
        destruct (Int256.eq key (caller context)) eqn:SSCase.
        apply Int256eq_true in SSCase.
        rewrite SSCase in H3.
        rewrite Int256Tree.gss in H3.
        inversion H3.
        clear -callvalue_bounded_prf.
        lia.
        apply Int256eq_false in SSCase. 
        rewrite Int256Tree.gso in H3 by assumption.
        apply H1 in H3.
        assumption.
    + 
      Check case_getFunds_prf.
      idtac.
      Transparent Crowdfunding_getFunds_opt.
      pose proof case_getFunds_prf as case_getFunds_prf'.
      unfold Crowdfunding_getFunds_opt in case_getFunds_prf'.
      unfold stepOnce.
      unfold step.
      rewrite Case.
      simpl in case_getFunds_prf.
      clear Case.
      unfold  address_accepts_funds_assumption in *.
      ds_inv; subst; try discriminate.
      unfold me_transfer in case_getFunds_prf'2.
      unfold make_machine_env in case_getFunds_prf'2.
      simpl in *.
      destruct (noOverflowOrUnderflowInTransfer
      contract_address
      (Crowdfunding_owner
         (contract_state (Step_state prev)))
      (ContractModel.update_balances
         (caller context) contract_address
         (callvalue context)
         (balance (Step_state prev))
         contract_address)
      (ContractModel.update_balances
         (caller context) contract_address
         (callvalue context)
         (balance (Step_state prev)))).
            simpl in *.
            inversion case_getFunds_prf'2.
            unfold next_blockchain_state; simpl.
            unfold balance_backed; simpl.
            intros; discriminate.
            unfold balance_backed; simpl.
            intros; discriminate.
            clear case_getFunds_prf.
            unfold balance_backed in IHReachableFromBy.
            unfold next_blockchain_state.
            unfold balance_backed.
            simpl.
            intros.
            apply IHReachableFromBy in H0.
            unfold new_balance_after_contract_call.
            pose proof (NoLeftoverOutgoings H).
            rewrite H1.
            simpl.
            unfold step; unfold balance_backed; simpl in *.
            apply Z.eqb_eq in H6.
            rewrite H6.
            rewrite addZeroBalance.
            assumption.
            clear case_getFunds_prf.
            unfold balance_backed in IHReachableFromBy.
            unfold next_blockchain_state.
            unfold balance_backed.
            simpl.
            intros.
            apply IHReachableFromBy in H0.
            unfold new_balance_after_contract_call. 
            pose proof (NoLeftoverOutgoings H). 
            rewrite H1. 
            simpl. 
            unfold step; unfold balance_backed; simpl in *. 
            apply Z.eqb_eq in H6.
            rewrite H6.
            rewrite addZeroBalance.
            assumption.
            clear case_getFunds_prf.
            unfold balance_backed in IHReachableFromBy.
            unfold next_blockchain_state.
            unfold balance_backed.
            simpl.
            intros.
            apply IHReachableFromBy in H0.
            unfold new_balance_after_contract_call.
            pose proof (NoLeftoverOutgoings H).
            rewrite H1.
            simpl.
            unfold step; unfold balance_backed; simpl in *.
            apply Z.eqb_eq in H6.
            rewrite H6.
            rewrite addZeroBalance.
            assumption.
    + 
      Check case_claim_prf.
      idtac.
      Transparent Crowdfunding_claim_opt.
      pose proof case_claim_prf as case_claim_prf'.
      unfold Crowdfunding_claim_opt in case_claim_prf'.
      unfold stepOnce.
      unfold step.
      rewrite Case.
      simpl in case_claim_prf.
      clear Case.
      unfold  address_accepts_funds_assumption in *.
      ds_inv; subst; try discriminate.
      *
       simpl in H6. 
       pose proof (NoLeftoverOutgoings H).
       apply balance_backed_in_processed_state; try assumption.
       *
       simpl in H6. 
       pose proof (NoLeftoverOutgoings H).
       apply balance_backed_in_processed_state; try assumption.
      * 
      simpl in *.
      destruct (noOverflowOrUnderflowInTransfer
      contract_address (caller context)
      (get_default 0 (caller context)
         (Crowdfunding_backers
            (contract_state (Step_state prev))))
      (ContractModel.update_balances
         (caller context) contract_address
         (callvalue context)
         (balance (Step_state prev)))) eqn:SCase.
      --
       simpl in *.
        inversion case_claim_prf'1.
        unfold balance_backed; simpl.
        intros.
        apply IHReachableFromBy in H0.
        unfold new_balance_after_contract_call.
        unfold update_Outgoing_transfer_recipient_and_amount. 
        simpl.
        unfold update_balances.
        simpl.
        rewrite negb_true_iff in H2.
        rewrite H2.
        rewrite Int256.eq_true.
        rewrite Int256.eq_sym in H2.
        rewrite H2.
        split.
        ++
           match goal with H : (callvalue context =? 0) = true |- _ => apply Z.eqb_eq in H end.
           match goal with H : (callvalue context = 0) |- _ => rewrite H end.
           repeat rewrite Z.add_0_r.
           match goal with H : _ /\ _ |- _ => destruct H end.
           apply Int256Tree_sum_minus.
           assumption.
        ++
         match goal with H : _ /\ _ |- _ => destruct H end.
           intros.
            destruct (Int256.eq key (caller context)) eqn:SSCase.
           **
            apply Int256eq_true in SSCase.
              match goal with H : context[get key] |- _ => rewrite SSCase in H end.
              match goal with H :  get _ (set _ _ _) = _ |- _ => rewrite Int256Tree.gss in H; inversion H end.
              lia.
           **
            apply Int256eq_false in SSCase.
              match goal with H : context[get key] |- _ => rewrite Int256Tree.gso in H by assumption end.
              match goal with H1 : (forall k v, get k _ = Some v -> v >= 0 /\ v < Int256.modulus),
                              H2 : (get key _ = _) |- _ => 
              apply H1 in H2; assumption
              end.
           --
            simpl in *.
             discriminate.
             + (* Case *)
      unfold stepOnce, step.
      rewrite Case.
      unfold balance_backed.
      unfold update_balance.
      simpl.
      destruct prf.
       destruct a.
      intros.
      apply IHReachableFromBy in H0.
      unfold update_balances.
      destruct (Int256.eq sender recipient); try assumption.
      destruct (Int256.eq contract_address sender) eqn:SCase.
        *
         apply Int256eq_true in SCase.
          symmetry in SCase.
           contradiction.
        *
         destruct(Int256.eq contract_address recipient) eqn:SSCase.
          --
           apply Int256eq_true in SSCase.
            rewrite <- SSCase.
             split; [|apply H0].
              lia.
          --
           split; apply H0.
           + (* Case IHReachableFromBy *)
            unfold stepOnce, step.
            rewrite Case.
            unfold balance_backed; simpl.
            unfold balance_backed in IHReachableFromBy.
            simpl in *.
            Check IHReachableFromBy.
            idtac.
            apply IHReachableFromBy.
            + (* Case IHReachableFromBy *)
            unfold stepOnce, step.
            rewrite Case. (* IHReachableFromBy *)
            apply IHReachableFromBy.
Qed.

Opaque Crowdfunding_donate_opt Crowdfunding_getFunds_opt Crowdfunding_claim_opt.

(** * Backers Can Retrieve Their Donation Theorem *)

Theorem can_claim_back :
forall state s l backer_addr backed_amount,
  ReachableFromBy initial_state state s l ->
  backed_amount = Int256Tree.get_default 0 backer_addr
                   (Crowdfunding_backers (contract_state state)) ->
  contract_address <> backer_addr ->
  backed_amount > 0 ->
  (balance state backer_addr + backed_amount <? Int256.modulus) = true ->
  Crowdfunding_funded (contract_state state) = false ->
  balance state contract_address < (Crowdfunding_goal (contract_state state)) ->
  (forall a : addr, 0 <= balance state a < Int256.modulus) ->
  Int256.ltu
    (Crowdfunding_max_block (contract_state state)) (block_number state) = true ->
  exists (action : Action state),
          Outgoing_transfer_recipient_and_amount
            (contract_state (step_keep_transfer state action))
          = Some (backer_addr, backed_amount)
          /\
          match action with
          | call_Crowdfunding_donate context _ _ _ _ _ _ =>
              callvalue context = 0 /\ caller context = backer_addr
          | call_Crowdfunding_getFunds context _ _ _ _ _ _ =>
              callvalue context = 0 /\ caller context = backer_addr
          | call_Crowdfunding_claim context _ _ _ _ _ _ =>
              callvalue context = 0 /\ caller context = backer_addr
          | _ => False
          end.
Proof.
intros.
Check call_Crowdfunding_claim.
eexists
  (call_Crowdfunding_claim
    state
    {| origin := backer_addr;
       caller := backer_addr;
       callvalue := 0;
       coinbase := Int256.zero;
       chainid := Int256.zero 
    |}
    _ _ _ tt
    {| Outgoing_transfer_recipient_and_amount := (Some (backer_addr, backed_amount));
       Crowdfunding_owner := Crowdfunding_owner (contract_state state);
       Crowdfunding_max_block := Crowdfunding_max_block (contract_state state);
       Crowdfunding_goal := Crowdfunding_goal (contract_state state);
       Crowdfunding_backers :=
         set backer_addr 0 (Crowdfunding_backers (contract_state state));
       Crowdfunding_funded := Crowdfunding_funded (contract_state state);
    |} _).
    simpl.
split; [reflexivity|split; reflexivity].
Unshelve.
split.
simpl.
unfold Int256.modulus, two_power_nat. lia.
unfold Int256.modulus, two_power_nat. simpl.
lia.
assumption.
simpl.
unfold noOverflowOrUnderflowInTransfer.
rewrite Z.sub_0_r.
rewrite Z.add_0_r.
apply andb_true_intro.
split.
apply andb_true_intro.
split.
apply andb_true_intro.
split.
lia.
unfold Int256.modulus, two_power_nat. simpl. lia.
rewrite Z.geb_le. pose proof (H6 backer_addr). lia.
rewrite Z.ltb_lt. pose proof (H6 contract_address). lia.
Transparent Crowdfunding_claim_opt.
unfold Crowdfunding_claim_opt. simpl.
destruct((backer_addr =? contract_address)%int256) eqn:Case. apply Int256eq_true in Case. symmetry in Case. contradiction.
simpl.
destruct ((Int256.ltu (Crowdfunding_max_block (contract_state state)) (block_number state))) eqn:SCase; [|discriminate].
simpl.
destruct((get_default 0 backer_addr (Crowdfunding_backers (contract_state state)) =? 0)) eqn:SSCase.
apply Z.eqb_eq in SSCase. lia.
destruct ((Crowdfunding_funded (contract_state state))) eqn:SSSCase; [discriminate|].
destruct ((Crowdfunding_goal (contract_state state) <=? ContractModel.update_balances backer_addr contract_address 0 (balance state) contract_address)) eqn:SSSSCase.
rewrite Z.leb_le in SSSSCase.
rewrite addZeroBalance in SSSSCase. lia.
simpl.
unfold address_accepts_funds_assumption.
destruct (noOverflowOrUnderflowInTransfer contract_address backer_addr (get_default 0 backer_addr (Crowdfunding_backers (contract_state state))) (ContractModel.update_balances backer_addr contract_address 0 (balance state))) eqn:SSSSSCase.
   simpl.
   unfold update_Outgoing_transfer_recipient_and_amount.
   simpl.
   rewrite <- H0.
   rewrite SSSCase.
   reflexivity.
   simpl.
   unfold noOverflowOrUnderflowInTransfer in SSSSSCase.
   rewrite andb_false_iff in SSSSSCase.
   destruct SSSSSCase.
   exfalso.
   {
   assert((forall (k : Int256Tree.elt) (v : Z), Int256Tree.get k (Crowdfunding_backers (contract_state state)) = Some v -> v >= 0 /\ v < Int256.modulus) -> sum (Crowdfunding_backers (contract_state state)) <=
              balance state contract_address ->
              (balance state contract_address -
          Int256Tree.get_default 0 backer_addr
            (Crowdfunding_backers (contract_state state)) >=? 0) = true).
            {
              clear.
              intros.
              rewrite Z.geb_le.
              assert(Int256Tree.get_default 0 backer_addr (Crowdfunding_backers (contract_state state)) <= sum (Crowdfunding_backers (contract_state state))).
              apply sum_bound1; try assumption; try lia.
              intros. apply H in H1. destruct H1.
              lia.
              lia.
            }
            unfold ContractModel.update_balances in H8.
            rewrite Int256.eq_true in H8.
            rewrite Int256.eq_false in H8 by auto.
            rewrite Int256.eq_false in H8 by auto.
            rewrite Z.add_0_r in H8.
            pose proof sufficient_funds_safe as sufficient_funds_safe. (* sufficient_funds_safe *)
            unfold Safe in sufficient_funds_safe. (* H sufficient_funds_safe *)
            apply sufficient_funds_safe in H. (* H *)
            unfold balance_backed in H.
            destruct H. assumption.
            apply H9 in H; [|assumption].
            assert((0 <=?
            get_default 0 backer_addr
              (Crowdfunding_backers (contract_state state))) = true).
              unfold get_default.
              unfold Z32 in H10.
              pose proof (H10 backer_addr).
              destruct(@get Z backer_addr (Crowdfunding_backers (contract_state state))).
              pose proof (H11 z).
              assert (Some z = Some z) by reflexivity.
              apply H12 in H13.
              destruct H13.
              rewrite Z.leb_le. lia.
              rewrite Z.leb_le. lia.
            rewrite H11 in H8.
            assert((get_default 0 backer_addr
            (Crowdfunding_backers
               (contract_state state)) <?
          Int256.modulus) = true).
          unfold get_default.
              unfold Z32 in H10.
              pose proof (H10 backer_addr).
              destruct(@get Z backer_addr (Crowdfunding_backers (contract_state state))).
              pose proof (H12 z).
              assert (Some z = Some z) by reflexivity.
              apply H13 in H14.
              destruct H14.
              rewrite Z.ltb_lt. lia.
              rewrite Z.ltb_lt. unfold Int256.modulus, two_power_nat. lia.
            rewrite H12 in H8.
            rewrite H in H8.
            simpl in H8.
            discriminate.
   }
   exfalso. rewrite H0 in H3.
   unfold ContractModel.update_balances in H8.
   rewrite Int256.eq_true in H8.
            rewrite Int256.eq_false in H8 by auto.
            rewrite Z.sub_0_r in H8.
            clear -H3 H8 H0.
            lia.
Qed.

Opaque Crowdfunding_donate_opt Crowdfunding_getFunds_opt Crowdfunding_claim_opt.

End Blockchain_Model.

End FunctionalCorrectness.