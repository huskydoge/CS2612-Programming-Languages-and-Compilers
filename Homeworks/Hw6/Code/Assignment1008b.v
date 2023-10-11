Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import PL.SyntaxInCoq.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)


(** 请在Coq中证明下面性质：*)

Theorem exists_or : forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  + intros.
    - destruct H.
      destruct H.
      * left.
        exists x.
        apply H.
      * right.
        exists x.
        apply H.
  + intros.
    - destruct H.
      * destruct H.
        exists x.
        left.
        apply H.
      * destruct H.
        exists x.
        right.
        apply H.
Qed.
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)


(** 请在Coq中证明下面性质：*)

Theorem forall_or: forall (A: Type) (P Q: A -> Prop),
  (forall a: A, P a) \/ (forall a: A, Q a) ->
  (forall a: A, P a \/ Q a).
Proof.
  intros.
  destruct H.
  pose proof H a.
  left.
  apply H0.
  pose proof H a.
  right.
  apply H0.
Qed. 
  (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)


(** 请在Coq中证明下面性质：*)

Theorem forall_not: forall (X: Type) (P: X -> Prop),
  (forall x: X, ~ P x) -> ~ (exists x: X, P x).
Proof.
  intros.
  pose proof classic (exists x : X, P x).
  destruct H0.
  - destruct H0.
    pose proof H x.
    tauto.
  - apply H0.
Qed.
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)


(** 请在Coq中证明下面性质：*)

Theorem exists_not: forall (X: Type) (P: X -> Prop),
  (exists x: X, ~ P x) -> ~ (forall x: X, P x).
Proof.
  intros.
  pose proof classic (forall x : X, P x).
  destruct H0.
  - destruct H.
    pose proof H0 x.
    tauto.
  - apply H0.
Qed.

(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


