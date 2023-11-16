Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PL.SyntaxInCoq.
Require Import PL.PracticalDenotations.
Import Lang_While DntSem_While1 DntSem_While2.
Import EDenote CDenote.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 定义与例子 *)

Definition EVar': string -> expr := EVar.
Coercion EConst: Z >-> expr.
Coercion EVar: var_name >-> expr.
Coercion EVar': string >-> expr.
Notation "[[ e ]]" := e
  (at level 0, e custom expr_entry at level 99).
Notation "( x )" := x
  (in custom expr_entry, x custom expr_entry at level 99).
Notation "x" := x
  (in custom expr_entry at level 0, x constr at level 0).
Notation "f x" := (f x)
  (in custom expr_entry at level 1, only parsing,
   f custom expr_entry,
   x custom expr_entry at level 0).
Notation "x + y" := (EBinop OPlus x y)
  (in custom expr_entry at level 12, left associativity).
Notation "x - y" := (EBinop OMinus x y)
  (in custom expr_entry at level 12, left associativity).
Notation "x * y" := (EBinop OMul x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x / y" := (EBinop ODiv x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x % y" := (EBinop OMod x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x <= y" := (EBinop OLe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x < y" := (EBinop OLt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x >= y" := (EBinop OGe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x > y" := (EBinop OGt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x == y" := (EBinop OEq x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x != y" := (EBinop ONe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x && y" := (EBinop OAnd x y)
  (in custom expr_entry at level 14, left associativity).
Notation "x || y" := (EBinop OOr x y)
  (in custom expr_entry at level 15, left associativity).
Notation "! x" := (EUnop ONot x)
  (in custom expr_entry at level 10).
Notation "- x" := (EUnop ONeg x)
  (in custom expr_entry at level 10).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom expr_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom expr_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99,
   c2 custom expr_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99).

Notation "⟦ e ⟧" := (eval_expr e)
  (at level 0, only printing, e custom expr_entry at level 99).
Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom expr_entry at level 99).

Ltac any_eval x :=
  match goal with
  | |- EDenote => exact (eval_expr x)
  | |- CDenote => exact (eval_com x)
  | _ => match type of x with
         | expr => exact (eval_expr x)
         | com => exact (eval_com x)
         end
  end.

Notation "⟦ x ⟧" := (ltac:(any_eval x))
  (at level 0, only parsing, x custom expr_entry at level 99).

Notation "x × y" := (@Sets.test1 _ (y -> Prop) _ x)
  (no associativity, at level 61): sets_scope.

(** 表达式语义等价 *)

Record eequiv (e1 e2: expr): Prop := {
  nrm_eequiv:
    ⟦ e1 ⟧.(nrm) == ⟦ e2 ⟧.(nrm);
  err_eequiv:
    ⟦ e1 ⟧.(err) == ⟦ e2 ⟧.(err);
}.

(** 表达式精化关系 *)

Record erefine (e1 e2: expr): Prop := {
  nrm_erefine:
    ⟦ e1 ⟧.(nrm) ⊆ ⟦ e2 ⟧.(nrm) ∪ (⟦ e2 ⟧.(err) × int64);
  err_erefine:
    ⟦ e1 ⟧.(err) ⊆ ⟦ e2 ⟧.(err);
}.

(** 程序语句语义等价 *)

Record cequiv (c1 c2: com): Prop := {
  nrm_cequiv: ⟦ c1 ⟧.(nrm) == ⟦ c2 ⟧.(nrm);
  err_cequiv: ⟦ c1 ⟧.(err) == ⟦ c2 ⟧.(err);
  inf_cequiv: ⟦ c1 ⟧.(inf) == ⟦ c2 ⟧.(inf);
}.

(** 程序语句精化关系 *)

Record crefine (c1 c2: com): Prop := {
  nrm_crefine:
    ⟦ c1 ⟧.(nrm) ⊆ ⟦ c2 ⟧.(nrm) ∪ (⟦ c2 ⟧.(err) × state);
  err_crefine:
    ⟦ c1 ⟧.(err) ⊆ ⟦ c2 ⟧.(err);
  inf_crefine:
    ⟦ c1 ⟧.(inf) ⊆ ⟦ c2 ⟧.(inf) ∪ ⟦ c2 ⟧.(err);
}.

Notation "e1 '~=~' e2" := (eequiv e1 e2)
  (at level 69, only printing, no associativity).
Notation "e1 '<<=' e2" := (erefine e1 e2)
  (at level 69, only printing, no associativity).
Notation "c1 '~=~' c2" := (cequiv c1 c2)
  (at level 69, only printing, no associativity).
Notation "c1 '<<=' c2" := (crefine c1 c2)
  (at level 69, only printing, no associativity).

Ltac any_equiv x y :=
  match type of x with
  | expr => exact (eequiv x y)
  | com => exact (cequiv x y)
  | _ => match type of y with
         | expr => exact (eequiv x y)
         | com => exact (cequiv x y)
         end
  end.

Ltac any_refine x y :=
  match type of x with
  | expr => exact (erefine x y)
  | com => exact (crefine x y)
  | _ => match type of y with
         | expr => exact (erefine x y)
         | com => exact (crefine x y)
         end
  end.

Notation "x '~=~' y" := (ltac:(any_equiv x y))
  (at level 69, only parsing, no associativity).
Notation "x '<<=' y" := (ltac:(any_refine x y))
  (at level 69, only parsing, no associativity).

Notation "H '.(nrm_eequiv)'" := (nrm_eequiv _ _ H)
  (at level 1).
Notation "H '.(err_eequiv)'" := (err_eequiv _ _ H)
  (at level 1).
Notation "H '.(nrm_erefine)'" := (nrm_erefine _ _ H)
  (at level 1).
Notation "H '.(err_erefine)'" := (err_erefine _ _ H)
  (at level 1).
Notation "H '.(nrm_cequiv)'" := (nrm_cequiv _ _ H)
  (at level 1).
Notation "H '.(err_cequiv)'" := (err_cequiv _ _ H)
  (at level 1).
Notation "H '.(inf_cequiv)'" := (inf_cequiv _ _ H)
  (at level 1).
Notation "H '.(nrm_crefine)'" := (nrm_crefine _ _ H)
  (at level 1).
Notation "H '.(err_crefine)'" := (err_crefine _ _ H)
  (at level 1).
Notation "H '.(inf_crefine)'" := (inf_crefine _ _ H)
  (at level 1).

(** 精化的例子 *)

Lemma const_plus_const_refine: forall n m: Z,
  EConst (n + m) <<= [[n + m]].
(** 证明见Coq代码。*)
Proof.
  intros.
  assert (Int64.min_signed <= n <= Int64.max_signed \/
          n < Int64.min_signed \/
          n > Int64.max_signed) as Hn by lia.
  assert (Int64.min_signed <= m <= Int64.max_signed \/
          m < Int64.min_signed \/
          m > Int64.max_signed) as Hm by lia.
  split.
  + sets_unfold; intros s i ?.
    simpl in H.
    destruct H.
    destruct Hn; [destruct Hm |]; [left | right | right]; simpl; sets_unfold.
    - unfold arith_sem1_nrm, arith_compute1_nrm.
      exists (Int64.repr n), (Int64.repr m).
      pose proof Int64.signed_repr _ H1.
      pose proof Int64.signed_repr _ H2.
      rewrite H3, H4.
      tauto.
    - tauto.
    - tauto.
  + sets_unfold; intros s ?.
    simpl in H.
    simpl; sets_unfold.
    unfold arith_sem1_err, arith_compute1_err.
    destruct Hn; [destruct Hm |]; [right | left | left]; simpl; sets_unfold.
    - exists (Int64.repr n), (Int64.repr m).
      pose proof Int64.signed_repr _ H0.
      pose proof Int64.signed_repr _ H1.
      rewrite H2, H3.
      tauto.
    - tauto.
    - tauto.
Qed.

(** 语义等价的例子：顺序执行有结合律 *)

Theorem CSeq_assoc: forall (c1 c2 c3: com),
  [[c1; (c2; c3)]] ~=~ [[(c1; c2); c3]].
Proof.
  intros.
  split.
  + simpl.
    rewrite Rels_concat_assoc.
    reflexivity.
  + simpl.
    rewrite Rels_concat_union_distr_l.
    rewrite Sets_union_assoc.
    rewrite Rels_concat_assoc.
    reflexivity.
  + simpl.
    rewrite Rels_concat_union_distr_l.
    rewrite Sets_union_assoc.
    rewrite Rels_concat_assoc.
    reflexivity.
Qed.


Theorem CIf_CSeq: forall e c1 c2 c3,
  [[ if e then { c1 } else { c2 }; c3 ]] ~=~
  [[ if e then { c1; c3 } else { c2; c3 } ]].
Proof.
  intros.
  split.
  + simpl.
    rewrite <- ! Rels_concat_assoc.
    apply Rels_concat_union_distr_r.
  + simpl.
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite <- ! Rels_concat_assoc.
    sets_unfold; intros s; tauto.
  + simpl.
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite <- ! Rels_concat_assoc.
    sets_unfold; intros s; tauto.
Qed.




(** * 语义等价与精化的性质 *)


(** 接下去，我们介绍语义等价的两条重要性质。其一：语义等价是一种等价关系。  


    在Coq标准库中，_[Reflexive]_、_[Symmetric]_、_[Transitive]_以及
    _[Equivalence]_定义了自反性、对称性、传递性以及等价关系。下面证明中，我们统
    一使用了_[Instance]_关键字，而非之前证明中常用的_[Theorem]_与_[Lemma]_，我们
    将稍后再解释_[Instance]_关键字的特殊作用。*)

Instance eequiv_refl: Reflexive eequiv.
Proof.
  unfold Reflexive; intros.
  split.
  + reflexivity.
  + reflexivity.
Qed.

Instance eequiv_sym: Symmetric eequiv.
Proof.
  unfold Symmetric; intros.
  split.
  + rewrite H.(nrm_eequiv).
    reflexivity.
  + rewrite H.(err_eequiv).
    reflexivity.
Qed.

Instance eequiv_trans: Transitive eequiv.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_eequiv), H0.(nrm_eequiv).
    reflexivity.
  + rewrite H.(err_eequiv), H0.(err_eequiv).
    reflexivity.
Qed.

Instance eequiv_equiv: Equivalence eequiv.
Proof.
  split.
  + apply eequiv_refl.
  + apply eequiv_sym.
  + apply eequiv_trans.
Qed.

(** 下面还可以证明精化关系也具有自反性和传递性。*)

Instance erefine_refl: Reflexive erefine.
Proof.
  unfold Reflexive; intros.
  split.
  + apply Sets_included_union1.
  + reflexivity.
Qed.

Instance erefine_trans: Transitive erefine.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_erefine).
    rewrite H0.(nrm_erefine).
    rewrite H0.(err_erefine).
    sets_unfold; intros s1 s2; tauto.
  + rewrite H.(err_erefine).
    rewrite H0.(err_erefine).
    reflexivity.
Qed.

(** 并且精化关系在语义等价变换下不变。*)

Instance erefine_well_defined:
  Proper (eequiv ==> eequiv ==> iff) erefine.
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  + split.
    - rewrite <- H.(nrm_eequiv).
      rewrite <- H0.(nrm_eequiv).
      rewrite <- H0.(err_eequiv).
      apply H1.(nrm_erefine).
    - rewrite <- H.(err_eequiv).
      rewrite <- H0.(err_eequiv).
      apply H1.(err_erefine).
  + split.
    - rewrite H.(nrm_eequiv).
      rewrite H0.(nrm_eequiv).
      rewrite H0.(err_eequiv).
      apply H1.(nrm_erefine).
    - rewrite H.(err_eequiv).
      rewrite H0.(err_eequiv).
      apply H1.(err_erefine).
Qed.

(** 程序语句间的语义等价关系也是等价关系，程序语句间的精化关系也具有自反性与传递
    性。*)

Instance cequiv_refl: Reflexive cequiv.
Proof.
  unfold Reflexive; intros.
  split.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Instance cequiv_sym: Symmetric cequiv.
Proof.
  unfold Symmetric; intros.
  split.
  + rewrite H.(nrm_cequiv).
    reflexivity.
  + rewrite H.(err_cequiv).
    reflexivity.
  + rewrite H.(inf_cequiv).
    reflexivity.
Qed.

Instance cequiv_trans: Transitive cequiv.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_cequiv), H0.(nrm_cequiv).
    reflexivity.
  + rewrite H.(err_cequiv), H0.(err_cequiv).
    reflexivity.
  + rewrite H.(inf_cequiv), H0.(inf_cequiv).
    reflexivity.
Qed.

Instance cequiv_equiv: Equivalence cequiv.
Proof.
  split.
  + apply cequiv_refl.
  + apply cequiv_sym.
  + apply cequiv_trans.
Qed.

Instance crefine_refl: Reflexive crefine.
Proof.
  unfold Reflexive; intros.
  split.
  + apply Sets_included_union1.
  + reflexivity.
  + apply Sets_included_union1.
Qed.

Instance crefine_trans: Transitive crefine.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_crefine).
    rewrite H0.(nrm_crefine).
    rewrite H0.(err_crefine).
    sets_unfold; intros s1 s2; tauto.
  + rewrite H.(err_crefine).
    rewrite H0.(err_crefine).
    reflexivity.
  + rewrite H.(inf_crefine).
    rewrite H0.(inf_crefine).
    rewrite H0.(err_crefine).
    sets_unfold; intros s; tauto.
Qed.

Instance crefine_well_defined:
  Proper (cequiv ==> cequiv ==> iff) crefine.
Proof.
  unfold Proper, respectful; intros.
  split; intros.
  + split.
    - rewrite <- H.(nrm_cequiv).
      rewrite <- H0.(nrm_cequiv).
      rewrite <- H0.(err_cequiv).
      apply H1.(nrm_crefine).
    - rewrite <- H.(err_cequiv).
      rewrite <- H0.(err_cequiv).
      apply H1.(err_crefine).
    - rewrite <- H.(inf_cequiv).
      rewrite <- H0.(inf_cequiv).
      rewrite <- H0.(err_cequiv).
      apply H1.(inf_crefine).
  + split.
    - rewrite H.(nrm_cequiv).
      rewrite H0.(nrm_cequiv).
      rewrite H0.(err_cequiv).
      apply H1.(nrm_crefine).
    - rewrite H.(err_cequiv).
      rewrite H0.(err_cequiv).
      apply H1.(err_crefine).
    - rewrite H.(inf_cequiv).
      rewrite H0.(inf_cequiv).
      rewrite H0.(err_cequiv).
      apply H1.(inf_crefine).
Qed.



