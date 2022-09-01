Require Import DataTypeOps.
Require Import LayerCONTRACT.

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

Require Import ContractModel.
Import ContractModel.ContractModel.

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

Definition initial_state :=
  mkBlockchainState
    snapshot_timestamp
    snapshot_number
    snapshot_balances
    snapshot_blockhash
    init_global_abstract_data (* TODO, check if init_global_abstract_data is the right way to get initial contract data. *)
.

Context {HmemOps: MemoryModelOps mem}.
Context {memModelOps : MemoryModelOps mem}.

Context
  (contract_address : addr).

Context
  (address_accepts_funds : option ContractState -> addr -> addr -> wei -> bool).

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
   amalgamated into the revert case. This means only needing to prove
   the (typically) trivial revert case once, without losing generality. *)
Inductive Action (before : BlockchainState) :=
  | call_Crowdfunding_donate (context : CallContext)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling donate successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling donate successfully given the context (and arguments, if applicable) *)
      (case_donate_prf : 
          runStateT (Crowdfunding_donate_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
          = Some (r, contract_state_after))
  | call_Crowdfunding_getFunds (context : CallContext)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling getFunds successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling getFunds successfully given the context (and arguments, if applicable) *)
      (case_getFunds_prf : 
          runStateT (Crowdfunding_getFunds_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
          = Some (r, contract_state_after))
  | call_Crowdfunding_claim (context : CallContext)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
      r (* The return value of calling claim successfully given the context (and arguments, if applicable) *)
      contract_state_after (* The contract state after calling claim successfully given the context (and arguments, if applicable) *)
      (case_claim_prf : 
          runStateT (Crowdfunding_claim_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
          = Some (r, contract_state_after))
  | externalBalanceTransfer (sender recipient : addr) (amount : wei) (* Note that if wei is currently an int256, so it is guaranteed to be non-negative. If ever changed to using Z again an appropriate check would be needed in this definition. *)
      (prf : sender <> contract_address /\ 
        ((noOverflowOrUnderflowInTransfer sender recipient amount (balance before))
         && (address_accepts_funds_assumption None sender recipient amount) = true))
  | timePassing (block_count time_passing : int256)
                (prf : validTimeChange block_count time_passing (block_number before) (timestamp before) = true)
  | revert (* A no-op, or a call with some error resulting in no state change, such as a contract reverting during its code execution, or such as calling an invalid function when there is no fallback defined. TODO check that DeepSEA does not have any fallback function in generated bytecode. *).

Fixpoint step
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_Crowdfunding_donate context
    callvalue_prf r d_after case_donate_prf => 
      next_blockchain_state before d_after
| call_Crowdfunding_claim context
    callvalue_prf r d_after case_claim_prf => 
      next_blockchain_state before d_after
| call_Crowdfunding_getFunds context
    callvalue_prf r d_after case_getFunds_prf => 
      next_blockchain_state before d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| revert => before
end.

Definition resetTransfers (d : ContractState) : ContractState :=
  {|
  Crowdfunding_owner := Crowdfunding_owner d;
  Crowdfunding_max_block := Crowdfunding_max_block d;
  Crowdfunding_goal := Crowdfunding_goal d;
  Crowdfunding_backers := Crowdfunding_backers d;
  Crowdfunding_funded := Crowdfunding_funded d;
  Crowdfunding_deadlinePassed_msg := Crowdfunding_deadlinePassed_msg d;
  Crowdfunding_successfullyDonated_msg := Crowdfunding_successfullyDonated_msg d;
  Crowdfunding_alreadyDonated_msg := Crowdfunding_alreadyDonated_msg d;
  Crowdfunding_funded_msg := Crowdfunding_funded_msg d;
  Crowdfunding_failed_msg := Crowdfunding_failed_msg d;
  Crowdfunding_too_early_to_claim_funds_msg := Crowdfunding_too_early_to_claim_funds_msg d;
  Crowdfunding_too_early_to_reclaim_msg := Crowdfunding_too_early_to_reclaim_msg d;
  Crowdfunding_cannot_refund_msg := Crowdfunding_cannot_refund_msg d;
  Crowdfunding_here_is_your_money_msg := Crowdfunding_here_is_your_money_msg d;
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

Notation "Q `since` P `as-long-as` R" := (since_as_long P Q R) (at level 1).

Definition donation_recorded (a : addr) (amount : Z) (s : BlockchainState) :=
  Int256Tree.get_default 0 a (Crowdfunding_backers (contract_state s)) = amount /\ amount > 0.

Definition no_claims_from (a : addr) (s : Step) :=
  match Step_action s with
  | (call_Crowdfunding_claim _ a _ _ _) => False
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

Hint Unfold Z_bounded. (*Causes annoying issues, use autounfold in *. *)
  

Ltac destruct_and :=
  match goal with
    | [ H : (_ /\ _) |- _ ] => destruct H
  end.

(* The expanded version more closely mirrors the proof as it was first
     proven, before being written concisely. *)
Lemma donation_preserved_expanded_version (a : addr) (amount : Z):
               (donation_recorded a amount)
  `since`      (donation_recorded a amount)
  `as-long-as` (no_claims_from a).
    Proof.
      unfold since_as_long.
      intros.
      
      induction H; [assumption|].
      
      assert(donation_recorded a amount prevSt).
      apply IHReachableFromBy.
      intros.
      apply H1.
      apply in_cons; assumption.

      clear H0.
      clear IHReachableFromBy.
      unfold donation_recorded in *.
      destruct_and.
      split; [|assumption].

      reachableFromByLinks.

      assert (no_claims_from a prev).
      apply H1.
      destruct HReachableFromByLinkStepToList.
      subst.
      right. left. reflexivity.

      destruct prev; simpl in *; unfold stepOnceAndWrap, step in *; simpl in *.
      clear H1. (* no_claims_one, not needed this time? *)
      clear next_action.
      clear H. (* ReachableFromBy, no longer needed? *)
      clear HReachableFromByLinkStepToList.
      unfold no_claims_from in H3.
      unfold stepOnce. simpl.
      unfold donation_recorded in *.
      destruct Step_action0; simpl in *;
        rewrite <- HReachableFromByLinkStateToStep in *;
        clear HReachableFromByLinkStateToStep Step_state0.
        - Transparent Crowdfunding_donate_opt. unfold Crowdfunding_donate_opt in case_donate_prf.
          ds_inv; subst; simpl.
          + match goal with H : false = true |- _ => inversion H end.
          + destruct (a =? (caller context))%int256 eqn:Case.
            * apply Int256eq_true in Case. rewrite <- Case.
              rewrite get_default_ss.
              exfalso.
              subst.
              unfold make_machine_env in Heqb0; simpl in Heqb0.
              apply Z.eqb_eq in Heqb0.
              rewrite Heqb0 in H2.
              lia.
            * apply Int256eq_false in Case.
              apply get_default_so; assumption.
          + match goal with H : false = true |- _ => inversion H end.
        - Transparent Crowdfunding_getFunds_opt. unfold Crowdfunding_getFunds_opt in case_getFunds_prf.
          ds_inv; subst; simpl; try reflexivity.
        - contradiction.
        - assumption.
        - assumption.
        - assumption.
Qed. 
Opaque Crowdfunding_donate_opt Crowdfunding_getFunds_opt Crowdfunding_claim_opt.

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

Lemma donation_preserved (a : addr) (d : Z):
               (donation_recorded a d) 
  `since`      (donation_recorded a d)
  `as-long-as` (no_claims_from a).
Proof.
(* Proof of a temporal property. *)
unfold since_as_long. intros. induction H; [assumption|].
assert(donation_recorded a d prevSt) by (apply IHReachableFromBy;
intros; apply H1; apply in_cons; assumption).
clear H0 IHReachableFromBy. unfold donation_recorded in *. destruct_and.
split; [|assumption]. Hlinks. assert (no_claims_from a prev) by
(apply H1; destruct HL; subst; right; left; auto).
destruct prev; autounfold in *; simpl in *.
clear H1 H HL. unfold no_claims_from in H3.
unfold donation_recorded in *. destruct Step_action0; simpl in *;
rewrite <- HS in *; try contradiction; try assumption.
- Transparent Crowdfunding_donate_opt.
  unfold Crowdfunding_donate_opt in *. ds_inv; subst; simpl; inv_FT.
  destruct (a =? (caller context)) eqn:Case.
  + apply Int256eq_true in Case. rewrite <- Case.
    rewrite get_default_ss. exfalso. subst. simpl in *.
    apply Z.eqb_eq in Heqb0. rewrite Heqb0 in H2. lia.
  + apply Int256eq_false in Case. apply get_default_so; assumption.
- Transparent Crowdfunding_getFunds_opt.
  unfold Crowdfunding_getFunds_opt in *.
  ds_inv; subst; simpl; try reflexivity.
Qed.

Close Scope int256.

(* Safety property predicate *)
Definition Safe P :=
  forall state, Reachable state -> P state.
     
(* A safety property, describing that the smart contract has sufficient balance with regards to the smart contract's records of donors *)
Definition balance_backed state :=
  (Crowdfunding_funded (contract_state state)) = false
  -> 
  sum (Crowdfunding_backers (contract_state state))
    <= Int256.unsigned (balance state (contract_address)) /\
    (forall key value, get key (Crowdfunding_backers (contract_state state)) = Some value -> value >= 0).

(* One of three properties describing a correct crowdfunding contract *)
Lemma sufficient_funds_safe : Safe balance_backed.
Abort.

End Blockchain_Model.

End FunctionalCorrectness.