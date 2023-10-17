Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4.
Local Open Scope Z.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)

(** 下面我们定义一项简单的程序变换：右结合变换。例如，将_[(c1;c2);c3]_变换为
    _[c1;(c2;c3)]_。  

    首先，这里定义一个辅助函数，该函数假设_[c]_与_[c0]_已经是右结合的，计算
    _[c; c0]_转换后的结果*)

Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

(** 现在，可以在_[CSeq_right_assoc]_的基础上定义右结合变换_[right_assoc]_。*)

Fixpoint right_assoc (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      CSeq_right_assoc (right_assoc c1) (right_assoc c2)
  | CIf e c1 c2 =>
      CIf e (right_assoc c1) (right_assoc c2)
  | CWhile e c1 =>
      CWhile e (right_assoc c1)
  | _ =>
      c
  end.

(** 下面证明：经过右结合变换后，确实程序语句中不再有左结合的结构了。下面分为两步
    定义『无左结合结构』，即_[no_left_assoc]_。*)

Definition not_left_assoc (c: com): Prop :=
  match c with
  | CSeq (CSeq _ _) _ => False
  | _ => True
  end.

Fixpoint no_left_assoc (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_left_assoc c /\
      no_left_assoc c1 /\ no_left_assoc c2
  | CIf e c1 c2 =>
      no_left_assoc c1 /\ no_left_assoc c2
  | CWhile e c1 =>
      no_left_assoc c1
  | _ =>
      True
  end.

(** 证明也需要分两步进行。请先证明关于_[CSeq_right_assoc]_的引理。*)

Lemma CSeq_right_assoc_no_left_assoc: forall c c0,
  no_left_assoc c ->
  no_left_assoc c0 ->
  no_left_assoc (CSeq_right_assoc c c0).
Proof.
  intros c c0 Hc Hc0.
  induction c; simpl.
  - tauto.
  - tauto.
  - destruct Hc.
    tauto.
  - destruct Hc.
    tauto.
  - simpl in Hc.
    tauto.
Qed. 
(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 下面是需要证明的最终结论。*)

Theorem right_assoc_no_left_assoc: forall c,
  no_left_assoc (right_assoc c).
Proof.
  intros.
  induction c; simpl.
  - tauto.
  - tauto.
  - apply CSeq_right_assoc_no_left_assoc; tauto.
  - tauto.
  - tauto.
Qed.  
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)


(** 下面请分两步证明：_[right_assoc]_变换前后的程序是语义等价的。*)

Lemma CSeq_right_assoc_sound: forall c c0,
  eval_com (CSeq_right_assoc c c0) ==
  eval_com (CSeq c c0).
Proof.
  intros. simpl.
  induction c; simpl.
  - reflexivity.
  - reflexivity.
  - unfold seq_sem.
    rewrite IHc2.
    unfold seq_sem.
    rewrite Rels_concat_assoc.
    reflexivity.
  - unfold seq_sem.
    reflexivity.
  - unfold seq_sem.
    reflexivity.
Qed.


(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem right_assoc_sound: forall c,
  eval_com (right_assoc c) == eval_com c.
Proof.
  intros.
  induction c; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite CSeq_right_assoc_sound.
    unfold seq_sem.
    rewrite <- IHc2.
    rewrite <- IHc1.
    reflexivity.
  - unfold if_sem.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.
  - unfold while_sem.
    apply Sets_indexed_union_congr.
    intros n.
    induction n;simpl.
    + reflexivity.
    + rewrite IHn.
      rewrite IHc.
      reflexivity.

Qed.


 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

