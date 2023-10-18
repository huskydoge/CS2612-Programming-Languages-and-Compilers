Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics. Import SetsNotation.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       DntSem_SimpleWhile5.
Local Open Scope order_scope.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)


(** 请证明，如果_[f]_是一个单调函数，那么将其迭代_[n]_次后得到的函数依然是单调的。*)

Theorem iter_mono:
  forall {A: Type} `{PO: PartialOrder_Setoid A} (f: A -> A) (n: nat),
    mono f ->
    mono (fun a => Nat.iter n f a).
Proof.
  intros; simpl.
  induction n.
  * simpl.
    unfold mono.
    tauto.
  * simpl.
    unfold mono.
    intros.
    apply H,IHn,H0.
Qed.
   (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明Bourbaki-Witt不动点具有单调性。*)


Lemma BW_LFix_mono:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f g: A -> A),
    mono f ->
    continuous f ->
    mono g ->
    continuous g ->
    (forall a, f a <= g a) ->
    BW_LFix f <= BW_LFix g.
Proof.
  unfold BW_LFix.
  intros.
  pose proof iter_mono f. pose proof iter_mono g.
  apply oCPO_completeness.
  unfold increasing.
  induction n;simpl.
  - apply bot_is_least.
  - apply H. apply IHn.
  - unfold is_omega_ub.
    induction n;simpl.
    + apply bot_is_least.
    + pose proof H3 (Nat.iter n f bot).
      pose proof H1 (Nat.iter n f bot)(omega_lub (fun n : nat => Nat.iter n g bot)).
      apply H7 in IHn.
      pose proof BW_LFix_is_fix g H1 H2.
      unfold BW_LFix in H8.
      apply reflexivity_setoid in H8.
      transitivity (g (Nat.iter n f bot)). apply H6.
      transitivity (g (omega_lub (fun n : nat => Nat.iter n g bot))).
      apply IHn. apply H8.
Qed.

   (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


