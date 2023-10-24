Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)

(** 请在Coq中根据定义证明二元关系的连接“∘”与二元-一元关系的连接“∘”之间有分配律。 *)

Lemma Rels_concat22_concat21_assoc {A B C: Type}:
  forall
    (R1: A -> B -> Prop)
    (R2: B -> C -> Prop)
    (T: C -> Prop),
  R1 ∘ (R2 ∘ T) == (R1 ∘ R2) ∘ T.
Proof.
  Sets_unfold; intros.
  split.
  - intros.
    destruct H as [b [H1 H2]].
    destruct H2 as [c [H3 H4]].
    exists c.
    split.
    + exists b.
      tauto.
    + tauto.
  - intros.
    destruct H as [c [H1 H2]].
    destruct H1 as [b [H3 H4]].
    exists b.
    split.
    + tauto.
    + exists c.
      tauto.
Qed. 
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请在Coq中根据定义证明二元-一元关系的连接“∘”会保持集合包含关系。 *)

Lemma Rels_concat21_mono {A B: Type}:
  forall
    (R R': A -> B -> Prop)
    (T T': B -> Prop),
  R ⊆ R' ->
  T ⊆ T' ->
  R ∘ T ⊆ R' ∘ T'.
Proof.
  Sets_unfold; intros.
  destruct H1 as [b [H1 H2]].
  exists b.
  split.
  - specialize (H a b).
    tauto.
  - specialize (H0 b).
    tauto.
Qed.


(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)


(** 请在Coq中根据定义证明二元-一元关系的连接“∘”对并集的左分配律。 *)

Lemma Rels_concat_indexed_union_distr_l {A B: Type}:
  forall
    (R: A -> B -> Prop)
    (Ts: nat -> B -> Prop),
  R ∘ ⋃ Ts == ⋃ (fun n => R ∘ Ts n).
Proof.
  Sets_unfold; intros.
  split.
  - intros.
    destruct H as [b [H1 H2]].
    destruct H2 as [n H2].
    exists n,b.
    tauto.
  - intros.
    destruct H as [n [b [H1 H2]]].
    exists b.
    split.
    + tauto.
    + exists n.
      tauto.
Qed.

(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


