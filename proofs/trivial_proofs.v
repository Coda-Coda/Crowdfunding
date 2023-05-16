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

Require Import Syntax.
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

Require Import Syntax.
Print Trivial_boolToInt_opt.
Print Trivial_boolToInt.



Require Import String.

Definition Note := Prop.
Definition N (s:string) : Note := True.

Lemma trivial_example2 : forall input context before result after,
  let machine_environment := (make_machine_env contract_address before context (fun _ _ _ _ => true)) in
  runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
= Some (result, after)
-> result = 1 <-> input = true.
Proof.
  intros. (* .all -.h#machine_environment -.h#memModelOps *)
  Transparent Trivial_boolToInt_opt. (* .-h#* .h#H  *) unfold Trivial_boolToInt_opt in H. (* .-h#* .h#H  *)
  split; intros.
    - inv_runStateT_branching.
      + pose (N "Hello") as N. subst. auto.
      + subst. discriminate.
    - inv_runStateT_branching.
      + subst. auto.
      + discriminate.
  Qed.


Lemma trivial_exampleTracker2 : forall input context before result after,
  let machine_environment := (make_machine_env contract_address before context (fun _ _ _ _ => true)) in
  runStateT (Trivial_boolToIntTracker_opt input machine_environment) (contract_state before)
= Some (result, after)
-> result = 1 <-> input = true.
Proof.
  intros. (* .all -.h#machine_environment -.h#memModelOps *)
  Transparent Trivial_boolToIntTracker_opt. (* .-h#* .h#H  *) unfold Trivial_boolToIntTracker_opt in H. (* .-h#* .h#H  *)
  split; intros.
    - inv_runStateT_branching.
      + pose (N "Hello") as N. subst. auto.
      + subst. discriminate.
    - inv_runStateT_branching.
      + subst. auto.
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


(* ---- *)

Open Scope Z.

Definition wei := int256. (* TODO consider whether this should be a tagged type instead. *)
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

(* TODO this will probably need updating based on the definition of me_transfer *)
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

Module FunctionalCorrectness.

(*
The goal here is to, in a sense, quantify over an arbitrary snapshot of the Blockchain and then model all possible interactions after that point. In particular, modelling most precisely the smart contract.
*)

Section Blockchain_Model.

Context
  (snapshot_timestamp : int256)
  (snapshot_number : int256)
  (snapshot_blockhash : int256 -> int256)
  (snapshot_balances : addr -> wei). (* This also guarantees balances are non-negative. *)

Definition ContractState := global_abstract_data_type.

Context
  (address_accepts_funds : option ContractState -> addr -> addr -> wei -> bool).

Definition initial_state :=
  mkBlockchainState
    snapshot_timestamp
    snapshot_number
    snapshot_balances
    snapshot_blockhash
    init_global_abstract_data (* TODO, check if init_global_abstract_data is the right way to get initial contract data. *)
.

Context {HmemOps: MemoryModelOps mem}.

(* The following is a helpful alternative to suppose instead of using `address_accepts_funds` alone. But it must be assumed explicitly. *)
Definition address_accepts_funds_assumed_for_from_contract 
  d sender recipient amount :=
  if (sender =? contract_address)%int256 then true else
  address_accepts_funds d sender recipient amount.

Definition address_accepts_funds_assumption := address_accepts_funds_assumed_for_from_contract.
(* The current model also has the implicit assumption that the transfers to a smart contract during a function call via callvalue are always accepted by the contract.
   This could be changed by editing callvalue_prf in the definition of Action, similarly to how it is done for `externalBalanceTransfer` *)

Definition updateTimeAndBlock before block_count time_passing : BlockchainState :=
mkBlockchainState
  (time_passing + (timestamp before))%int256
  (block_count + (block_number before))%int256
  (balance before)
  (blockhash before)
  (contract_state before)
.

Definition validTimeChange block_count time_passing current_block_number current_timestamp : bool :=
  (* Note, testing for positive block_count and time_passing is unnecessary while they are Int256 values.
     It would be necessary to add positivity checks if using Z instead of course. *)
  ((Int256.intval block_count) + (Int256.intval current_block_number) <=? Int256.max_unsigned)%Z
  && ((Int256.intval time_passing) + (Int256.intval current_timestamp) <=? Int256.max_unsigned)%Z.

Open Scope int256.
Definition update_balances sender recipient amount balances : (addr -> wei) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => 
  if sender =? recipient then balances a else
    if a =? sender then (balances sender) - amount else
     if a =? recipient then (balances recipient) + amount
      else balances a.
Close Scope int256.

Definition update_balance before latest_balances : BlockchainState :=
  mkBlockchainState
  (timestamp before)
  (block_number before)
  latest_balances
  (blockhash before)
  (contract_state before)
.

Definition noOverflowOrUnderflowInTransfer (sender recipient : addr) (amount : wei) (balances : addr -> wei) : bool := 
  ((Int256.intval (balances sender)) - (Int256.intval amount) >=? 0)%Z
  && ((Int256.intval (balances recipient)) + (Int256.intval amount) <=? Int256.max_unsigned)%Z.

(* TODO-Review - This defines how balances are updated in the model after transferEth *)
Open Scope int256.
Definition current_balances 
  (* Note on where insufficient balance-checking takes place:
     Overflow and underflow of balances must already have been checked before this function.
     (i.e. before a transfer is placed in Outgoing_transfer_recipient_and_amount it should
           have been checked to ensure no overflow/underflow.)
     Currently this check is expected to be implemented by the me_transfer definition.
     !! Ensure you are using an appropriate me_transfer definition. !! *)
  (successful_transfer : option (addr * wei))
  (initial_balances : addr -> wei) 
  : (addr -> wei) :=
    match successful_transfer with
      | None => initial_balances
      | Some (recipient, amount) => 
          update_balances contract_address recipient amount initial_balances
    end.
Close Scope int256.

Definition new_balance_after_contract_call (before : BlockchainState) (d : ContractState) : (addr -> wei) :=
    (current_balances
      (Outgoing_transfer_recipient_and_amount d)
      (balance before)).

Definition next_blockchain_state (before : BlockchainState) (d : ContractState) : BlockchainState :=
  mkBlockchainState
    (timestamp before)
    (block_number before)
    (new_balance_after_contract_call before d)
    (blockhash before)
    d.

(* This approach to defining Action requires all calls to a contract
   function to succeed, i.e. return (Some _ _), failure cases are
   amalgamated into the no_op case. This means only needing to prove
   the (typically) trivial no_op case once, without losing generality. *)
Inductive Action (before : BlockchainState) :=
  | call_Trivial_boolToInt (b: bool) (context : CallContext)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling donate successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling donate successfully given the context (and arguments, if applicable) *)
      (case_donate_prf : 
          runStateT (Trivial_boolToInt_opt b (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
          = Some (r, contract_state_after))
  | call_Trivial_boolToIntTracker (b: bool) (context : CallContext)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling donate successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling donate successfully given the context (and arguments, if applicable) *)
      (case_donate_prf : 
          runStateT (Trivial_boolToIntTracker_opt b (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
          = Some (r, contract_state_after))
  | externalBalanceTransfer (sender recipient : addr) (amount : wei) (* Note that if wei is currently an int256, so it is guaranteed to be non-negative. If ever changed to using Z again an appropriate check would be needed in this definition. *)
      (prf : sender <> contract_address /\ 
        ((noOverflowOrUnderflowInTransfer sender recipient amount (balance before))
         && (address_accepts_funds_assumption None sender recipient amount) = true))
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (block_number before) (timestamp before) = true)
  | no_op (* A no-op, or a call with some error resulting in no state change, such as a contract reverting during its code execution, or such as calling an invalid function when there is no fallback defined. TODO check that DeepSEA does not have any fallback function in generated bytecode. *).

Definition step
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_Trivial_boolToInt b context
    callvalue_prf r d_after case_donate_prf => 
      next_blockchain_state before d_after
| call_Trivial_boolToIntTracker b context
    callvalue_prf r d_after case_claim_prf => 
      next_blockchain_state before d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| no_op => before
end.

Definition resetTransfers (d : ContractState) : ContractState :=
  {|
  Trivial_seenTrueYet := Trivial_seenTrueYet d;
  Outgoing_transfer_recipient_and_amount := None
|}.

Record Step := mkStep
  {
    Step_state : BlockchainState;
    Step_action : Action Step_state
  }.

Record StepSpace := mkStepSpace
  {
    StepSpace_state : BlockchainState;
    StepSpace_actions : Type
  }.

Class Next (b : BlockchainState) : Type :=
{
    next : Action b -> BlockchainState
}.

Instance : Next initial_state :=
{
  next := step initial_state
}.


Definition InSecond (st : BlockchainState) := 
   exists (a : Action initial_state), st = step initial_state a.

Definition InThird (st : BlockchainState) := 
    exists (two : BlockchainState) (a : Action two) ,
      InSecond two /\ st = step two a.

Definition InFourth (st : BlockchainState) := 
  exists (three : BlockchainState) (a : Action three) ,
    InThird three /\ st = step three a.

Open Scope nat.
Inductive InPossible (st : BlockchainState) (n:nat) :=
  | inzero (H : exists (a : Action initial_state), st = step initial_state a) (Hn : n = 0) : InPossible st n
  | inSn (current : BlockchainState) (Hs : InPossible current (n - 1)) 
  
  (
    H : exists (a : Action current),
    st = step current a
  )
  : InPossible st n
  
  .
Close Scope nat.

Definition stepOnce prev := (step (Step_state prev) (Step_action prev)).
Definition stepOnceAndWrap prev next_action := (mkStep (stepOnce prev) next_action).
Hint Unfold stepOnce stepOnceAndWrap.

Inductive ReachableFromBy from : BlockchainState -> Step -> list Step -> Prop :=
| initial_case (next_action : Action from)
    : ReachableFromBy from from (mkStep from next_action) [mkStep from next_action]
| step_case (prevSt : BlockchainState) (prev : Step) (prevList : list Step)
            (Hprev : ReachableFromBy from prevSt prev prevList)
    (next_action : Action (stepOnce prev))
    : ReachableFromBy from  (stepOnce prev) 
     (stepOnceAndWrap prev next_action)
     (stepOnceAndWrap prev next_action :: prevList)  .

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


(* Ugh *)
(* Inductive ReachableFromBy from (s : BlockchainState) (next_action : Action s) : list Step -> Prop :=
| initial_case (first_action : Action from)
    : ReachableFromBy from from first_action [mkStep from first_action]
| step_case (prevList : list Step) (Hprev : ReachableFromBy from s next_action prevList)
    (next_step_action : Action (step s next_action))
    : ReachableFromBy from (step s next_action) next_step_action
     (stepOnce s next_action next_step_action :: prevList)  
. *)

Definition ReachableFrom from state := exists l step', ReachableFromBy from state step' l.

Definition Reachable := ReachableFrom initial_state.

Definition since_as_long (P : BlockchainState -> Prop) (Q : BlockchainState -> Prop) (R : Step -> Prop) :=
  forall sc st st' step',
    ReachableFromBy st st' step' sc ->
    P st ->
    (forall sa, List.In sa sc -> R sa) ->
    Q st'.    
    
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
            Notation "Q `since` P `as-long-as` R" := (since_as_long P Q R) (at level 1).
    
  
Hint Unfold Z_bounded. (*Causes annoying issues, use autounfold in *. *)
  

Ltac destruct_and :=
  match goal with
    | [ H : (_ /\ _) |- _ ] => destruct H
  end.

(* ---- *)

(* Abandoned: *)

(*
Lemma trivial_example3 : forall s st sc,
  ReachableFromBy initial_state s st sc
  -> Trivial_seenTrueYet (contract_state s) = true
  -> (
    exists sa, List.In sa sc 
      -> match Step_action sa with
         | call_Trivial_boolToIntTracker b _ _ _ _ _ => b = true
         | _ => False
         end)
  .
Proof.
  intros.
  induction H.
  - simpl. exists ({| Step_state := initial_state; Step_action := next_action |}).
    intros.
    destruct H.
    simpl.
    destruct next_action; simpl.
    Transparent Trivial_boolToInt_opt. unfold Trivial_boolToInt_opt in case_donate_prf.
    inv_runStateT_branching.
    destruct b.
    simpl in *.
    discriminate.
    discriminate.
    Transparent Trivial_boolToIntTracker_opt. unfold Trivial_boolToIntTracker_opt in case_donate_prf.
    inv_runStateT_branching.
    destruct b.
    reflexivity.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    simpl. contradiction.
  - apply IHReachableFromBy.
   exfalso.
    pose proof (H0 {| Step_state := initial_state; Step_action := next_action |}).
    simpl in H. 
    
*)