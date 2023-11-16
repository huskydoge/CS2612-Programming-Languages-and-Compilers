Require Import Coq.Classes.RelationClasses.
Require Import PL.DenotationalSemantics.
Require Import PL.PracticalDenotations.
Import BWFix KTFix.
Local Open Scope order_scope.

(************)
(** 习题：  *)
(************)


(** 请证明下面关于Knaster-Tarski最大不动点的性质。 *)
Print lub_sound.
Lemma KT_GFix_mono:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f g: A -> A),
    mono f ->
    mono g ->
    (forall a, f a <= g a) ->
    KT_GFix f <= KT_GFix g.
Proof.
  intros.
  unfold KT_GFix.
  apply lub_tight.
  unfold is_ub.
  intros.
  assert (a' <= g a').
  specialize (H1 a').
  transitivity (f a'); auto.
  apply lub_sound.
  tauto.
Qed.


  (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)


(** 很显然，任意完备格上都有最小元，它可以被定义为空集的上确界。*)

Definition bot
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}: A :=
  lub (fun _ => False).

(** 下面请你证明，空集的上确界确实是最小元。*)
Lemma bot_is_least
        {A: Type}
        `{CLA: CompleteLattice_Setoid A}:
  forall a: A, bot <= a.
Proof.
  intros.
  unfold bot.
  apply lub_tight.
  unfold is_ub.
  tauto.
Qed.
  (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)


(** 我们已经学过，在完备偏序集上，单调连续函数_[f]_的最小不动点可以定义为   

        _[bot]_, _[f bot]_, _[f (f bot)]_, ...   

    的上确界。那么在完备格上，如果_[f]_是一个单调函数，上面这个计算结果是不动点吗？下面
    是这一计算结果的Coq定义*)

Definition BW
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}
             (f: A -> A) :=
  lub (fun a => exists n: nat, a = Nat.iter n f bot).

(** 请你证明以下结论。*)

Lemma CL_mono_KT:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    BW f <= KT_GFix f.
Proof.
  intros.
  unfold BW, KT_GFix.
  apply lub_tight. unfold is_ub.
  intros.
  destruct H0;rewrite H0.
  apply lub_sound.
  assert (forall n, Nat.iter n f bot <= f (Nat.iter n f bot)).
  induction n;simpl.
  - apply bot_is_least.
  - apply H;apply IHn.
  - apply H1.
Qed.

    (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

