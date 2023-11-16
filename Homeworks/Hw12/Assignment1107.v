Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics.
Require Import PL.PracticalDenotations.
Require Import PL.EquivAndRefine.
Import Lang_While DntSem_While1 DntSem_While2.
Import EDenote CDenote.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)


(** 请证明语义等价。*)

Theorem CSeq_CSkip: forall c,
  [[ c; skip ]] ~=~ c.
Proof.
  intros.
  split;simpl.
  - intros.
    apply Rels_concat_id_r.
  - intros.
    rewrite Rels_concat_empty_r.
    rewrite Sets_union_empty.
    apply reflexivity.
  - intros.
    rewrite Rels_concat_empty_r.
    rewrite Sets_union_empty.
    apply reflexivity.
Qed.



(************)
(** 习题：  *)
(************)


(** 请证明语义等价。*)

Theorem CSkip_CSeq: forall c,
  [[ skip; c ]] ~=~ c.
Proof.
  intros.
  split;simpl.
  - intros.
    apply Rels_concat_id_l.
  - intros.
    rewrite Rels_concat_id_l.
    rewrite Sets_empty_union.
    apply reflexivity.
  - intros.
    rewrite Rels_concat_id_l.
    rewrite Sets_empty_union.
    apply reflexivity.
Qed.

