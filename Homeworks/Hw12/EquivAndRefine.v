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
Require Import PL.DenotationalSemantics. Import BWFix Sets_CPO.
Require Import PL.PracticalDenotations. Import KTFix Sets_CL.
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



(** 两条重要性质之二是：所有语法连接词能保持语义等价关系（congruence），也能保持精化关系（monotonicity）。下面先证明加法、减法、乘法的情况。*)

Lemma add_congr: forall (e11 e12 e21 e22: expr),
    e11 ~=~ e12 ->
    e21 ~=~ e22 ->
    (EBinop OPlus e11 e21) ~=~ (EBinop OPlus e12 e22).
Proof.
  intros.
  split.
  + simpl. admit.
  + simpl.
Abort.

(** Normal 对应相同 *)
Lemma arith_sem1_nrm_congr: forall Zfun (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  arith_sem1_nrm Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  arith_sem1_nrm Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? ? s i.
  unfold arith_sem1_nrm.
  apply ex_iff_morphism; intros i1. (*脱掉i1*)
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |]. (** [apply H |] *)
  apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
  reflexivity.
Qed.


(** Error 对应相同 *)
Lemma arith_sem1_err_congr: forall Zfun (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
  arith_sem1_err Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
  arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? ? s.
  unfold arith_sem1_err.
  apply or_iff_morphism.
  + apply or_iff_morphism.
    - apply H.(err_eequiv).
    - apply H0.(err_eequiv).
  + apply ex_iff_morphism; intros i1.
    apply ex_iff_morphism; intros i2.
    apply and_iff_morphism; [apply H.(nrm_eequiv) |].
    apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
    reflexivity.
Qed.

Lemma arith_sem1_nrm_mono: forall Zfun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  arith_sem1_nrm Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  arith_sem1_nrm Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ∪
  ((⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
    arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm)) × int64).
Proof.
  intros.
  sets_unfold.
  intros s i.
  unfold arith_sem1_nrm, arith_sem1_err.
  intros [i1 [i2 [? [? ?] ] ] ].
  apply H.(nrm_erefine) in H1. (**根据精化关系*)
  apply H0.(nrm_erefine) in H2.
  sets_unfold in H1.
  sets_unfold in H2.
  destruct H1; [| tauto].
  destruct H2; [| tauto].
  left. (** 只剩下最后一种求值都成功的情况 *)
  exists i1, i2.
  tauto.
Qed.

(**证明精化后出错变少*)
Lemma arith_sem1_err_mono: forall Zfun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
  arith_sem1_err Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
  arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  intros.
  sets_unfold.
  intros s.
  unfold arith_sem1_err.
  intros [ [? | ?] | [i1 [i2 [? [? ?] ] ] ] ].
  + apply H.(err_erefine) in H1.
    tauto.
  + apply H0.(err_erefine) in H1.
    tauto.
  + apply H.(nrm_erefine) in H1.
    apply H0.(nrm_erefine) in H2.
    sets_unfold in H1.
    sets_unfold in H2.
    destruct H1; [| tauto].
    destruct H2; [| tauto].
    right. (** 选择最右边的那一种 *)
    exists i1, i2.
    tauto.
Qed.

(** 很多其它情况的证明是类似的。*)

Lemma arith_sem2_nrm_congr: forall int64fun (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  arith_sem2_nrm int64fun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  arith_sem2_nrm int64fun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? ? s i.
  unfold arith_sem2_nrm.
  apply ex_iff_morphism; intros i1.
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma arith_sem2_err_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
  arith_sem2_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
  arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s.
  unfold arith_sem2_err.
  apply or_iff_morphism.
  + apply or_iff_morphism.
    - apply H.(err_eequiv).
    - apply H0.(err_eequiv).
  + apply ex_iff_morphism; intros i1.
    apply ex_iff_morphism; intros i2.
    apply and_iff_morphism; [apply H.(nrm_eequiv) |].
    apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
    reflexivity.
Qed.

Lemma arith_sem2_nrm_mono: forall int64fun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  arith_sem2_nrm int64fun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  arith_sem2_nrm int64fun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ∪
  ((⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
    arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm)) × int64).
Proof.
  intros.
  sets_unfold.
  intros s i.
  unfold arith_sem2_nrm, arith_sem2_err.
  intros [i1 [i2 [? [? ?] ] ] ].
  apply H.(nrm_erefine) in H1.
  apply H0.(nrm_erefine) in H2.
  sets_unfold in H1.
  sets_unfold in H2.
  destruct H1; [| tauto].
  destruct H2; [| tauto].
  left.
  exists i1, i2.
  tauto.
Qed.

Lemma arith_sem2_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
  arith_sem2_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
  arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  intros.
  sets_unfold.
  intros s.
  unfold arith_sem2_err.
  intros [ [? | ?] | [i1 [i2 [? [? ?] ] ] ] ].
  + apply H.(err_erefine) in H1.
    tauto.
  + apply H0.(err_erefine) in H1.
    tauto.
  + apply H.(nrm_erefine) in H1.
    apply H0.(nrm_erefine) in H2.
    sets_unfold in H1.
    sets_unfold in H2.
    destruct H1; [| tauto].
    destruct H2; [| tauto].
    right.
    exists i1, i2.
    tauto.
Qed.

Lemma cmp_sem_nrm_congr: forall op (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  cmp_sem_nrm op ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  cmp_sem_nrm op ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? ? s i.
  unfold cmp_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma cmp_sem_err_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ==
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s.
  apply or_iff_morphism.
  + apply H.(err_eequiv).
  + apply H0.(err_eequiv).
Qed.

(** comparison 本身不会出错 *)
Lemma cmp_sem_nrm_mono: forall op (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  cmp_sem_nrm op ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  cmp_sem_nrm op ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ∪
  ((⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err)) × int64).
Proof.
  intros.
  sets_unfold.
  intros s i.
  unfold cmp_sem_nrm.
  intros [i1 [i2 [? [? ?] ] ] ].
  apply H.(nrm_erefine) in H1.
  apply H0.(nrm_erefine) in H2.
  sets_unfold in H1.
  sets_unfold in H2.
  destruct H1; [| tauto].
  destruct H2; [| tauto].
  left.
  exists i1, i2.
  tauto.
Qed.

Lemma cmp_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  ⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ⊆
  ⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err).
Proof.
  intros.
  sets_unfold.
  intros s.
  intros [? | ?].
  + apply H.(err_erefine) in H1.
    tauto.
  + apply H0.(err_erefine) in H1.
    tauto.
Qed.

(** 短路求值，求值成功的情况  *)
Lemma and_sem_nrm_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  and_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  and_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s i.
  unfold and_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |]. (** 左半边*)
  apply or_iff_morphism; [reflexivity |].
  apply and_iff_morphism; [reflexivity |].
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma and_sem_err_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  ⟦ e11 ⟧.(err) ∪ and_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err) ==
  ⟦ e12 ⟧.(err) ∪ and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s.
  unfold and_sem_err.
  apply or_iff_morphism; [apply H.(err_eequiv) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  apply and_iff_morphism; [| apply H0.(err_eequiv)].
  reflexivity.
Qed.

Lemma and_sem_nrm_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  and_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  and_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ∪
  ((⟦ e12 ⟧.(err) ∪ and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err)) × int64).
Proof.
  intros.
  sets_unfold.
  intros s i.
  unfold and_sem_nrm, and_sem_err.
  intros [i1 ?].
  destruct H1.
  apply H.(nrm_erefine) in H1.
  sets_unfold in H1.
  destruct H1; [| tauto].
  destruct H2; [left; exists i1; tauto |].
  destruct H2 as [? [i2 [? ?] ] ].
  apply H0.(nrm_erefine) in H3.
  sets_unfold in H3.
  destruct H3; [| right; right; exists i1; tauto].
  left; exists i1.
  split; [tauto |].
  right.
  split; [tauto |].
  exists i2; tauto.
Qed.

Lemma and_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  ⟦ e11 ⟧.(err) ∪ and_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err) ⊆
  ⟦ e12 ⟧.(err) ∪ and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err).
Proof.
  intros.
  sets_unfold.
  intros s.
  unfold and_sem_err.
  intros [? | ?]; [left; apply H.(err_erefine); tauto |].
  destruct H1 as [i1 [? [? ?] ] ].
  apply H.(nrm_erefine) in H1.
  sets_unfold in H1.
  destruct H1; [| tauto].
  right; exists i1.
  apply H0.(err_erefine) in H3.
  tauto.
Qed.

Lemma or_sem_nrm_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  or_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ==
  or_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s i.
  unfold or_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  apply or_iff_morphism; [reflexivity |].
  apply and_iff_morphism; [reflexivity |].
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H0.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma or_sem_err_congr: forall (e11 e12 e21 e22: expr),
  e11 ~=~ e12 ->
  e21 ~=~ e22 ->
  ⟦ e11 ⟧.(err) ∪ or_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err) ==
  ⟦ e12 ⟧.(err) ∪ or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err).
Proof.
  sets_unfold.
  intros ? ? ? ? ? ? s.
  unfold or_sem_err.
  apply or_iff_morphism; [apply H.(err_eequiv) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  apply and_iff_morphism; [| apply H0.(err_eequiv)].
  reflexivity.
Qed.

Lemma or_sem_nrm_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  or_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⊆
  or_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ∪
  ((⟦ e12 ⟧.(err) ∪ or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err)) × int64).
Proof.
  intros.
  sets_unfold.
  intros s i.
  unfold or_sem_nrm, or_sem_err.
  intros [i1 ?].
  destruct H1.
  apply H.(nrm_erefine) in H1.
  sets_unfold in H1.
  destruct H1; [| tauto].
  destruct H2; [left; exists i1; tauto |].
  destruct H2 as [? [i2 [? ?] ] ].
  apply H0.(nrm_erefine) in H3.
  sets_unfold in H3.
  destruct H3; [| right; right; exists i1; tauto].
  left; exists i1.
  split; [tauto |].
  right.
  split; [tauto |].
  exists i2; tauto.
Qed.

Lemma or_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  ⟦ e11 ⟧.(err) ∪ or_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err) ⊆
  ⟦ e12 ⟧.(err) ∪ or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err).
Proof.
  intros.
  sets_unfold.
  intros s.
  unfold or_sem_err.
  intros [? | ?]; [left; apply H.(err_erefine); tauto |].
  destruct H1 as [i1 [? [? ?] ] ].
  apply H.(nrm_erefine) in H1.
  sets_unfold in H1.
  destruct H1; [| tauto].
  right; exists i1.
  apply H0.(err_erefine) in H3.
  tauto.
Qed.

(** 下面把二元运算的情况汇总起来。*)
(** Proper: 表达式语法树的一个二元函数，如果这个二元函数的第一个参数做表达式语义等价变换，第二个也。。。,得到的符合eequiv性质*)

Instance EBinop_congr: forall op,
  Proper (eequiv ==> eequiv ==> eequiv) (EBinop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  (** 布尔二元运算的情况 *)
  + split.
    - apply or_sem_nrm_congr; tauto.
    - apply or_sem_err_congr; tauto.
  + split.
    - apply and_sem_nrm_congr; tauto.
    - apply and_sem_err_congr; tauto.
  (** 大小比较的情况 *)
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  + split.
    - apply cmp_sem_nrm_congr; tauto.
    - apply cmp_sem_err_congr; tauto.
  (** 加减乘运算的情况 *)
  + split.
    - apply arith_sem1_nrm_congr; tauto.
    - apply arith_sem1_err_congr; tauto.
  + split.
    - apply arith_sem1_nrm_congr; tauto.
    - apply arith_sem1_err_congr; tauto.
  + split.
    - apply arith_sem1_nrm_congr; tauto.
    - apply arith_sem1_err_congr; tauto.
  (** 除法与取余的情况 *)
  + split.
    - apply arith_sem2_nrm_congr; tauto.
    - apply arith_sem2_err_congr; tauto.
  + split.
    - apply arith_sem2_nrm_congr; tauto.
    - apply arith_sem2_err_congr; tauto.
Qed.

(** e1 + e2 => e1' + e2, e1'是e1的精化，精化有自反性，从而替换前后整体还是精化关系*)
Instance EBinop_mono: forall op,
  Proper (erefine ==> erefine ==> erefine) (EBinop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  (** 布尔二元运算的情况 *)
  + split.
    - simpl.
      apply (or_sem_nrm_mono x y x0 y0); tauto.
    - apply or_sem_err_mono; tauto.
  + split.
    - apply and_sem_nrm_mono; tauto.
    - apply and_sem_err_mono; tauto.
  (** 大小比较的情况 *)
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  (** 加减乘运算的情况 *)
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  (** 除法与取余的情况 *)
  + split.
    - apply arith_sem2_nrm_mono; tauto.
    - apply arith_sem2_err_mono; tauto.
  + split.
    - apply arith_sem2_nrm_mono; tauto.
    - apply arith_sem2_err_mono; tauto.
Qed.

(** 一元运算的情况是类似的。*)

Lemma not_sem_nrm_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  not_sem_nrm ⟦ e1 ⟧.(nrm) ==
  not_sem_nrm ⟦ e2 ⟧.(nrm).
Proof.
  unfold not_sem_nrm.
  sets_unfold.
  intros ? ? ? s i.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma not_sem_err_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  ⟦ e1 ⟧.(err) == ⟦ e2 ⟧.(err).
Proof.
  intros.
  apply H.(err_eequiv).
Qed.

Lemma not_sem_nrm_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  not_sem_nrm ⟦ e1 ⟧.(nrm) ⊆
  not_sem_nrm ⟦ e2 ⟧.(nrm) ∪ (⟦ e2 ⟧.(err) × int64).
Proof.
  unfold not_sem_nrm.
  sets_unfold.
  intros ? ? ? s i.
  intros [i1 [? ?] ].
  apply H.(nrm_erefine) in H0.
  sets_unfold in H0.
  destruct H0; [| tauto].
  left; exists i1.
  tauto.
Qed.

Lemma not_sem_err_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  ⟦ e1 ⟧.(err) ⊆ ⟦ e2 ⟧.(err).
Proof.
  intros.
  apply H.(err_erefine).
Qed.

Lemma neg_sem_nrm_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  neg_sem_nrm ⟦ e1 ⟧.(nrm) ==
  neg_sem_nrm ⟦ e2 ⟧.(nrm).
Proof.
  unfold neg_sem_nrm.
  sets_unfold.
  intros ? ? ? s i.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma neg_sem_err_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  ⟦ e1 ⟧.(err) ∪ neg_sem_err ⟦ e1 ⟧.(nrm) ==
  ⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm).
Proof.
  intros.
  unfold neg_sem_err; sets_unfold.
  intros s.
  apply or_iff_morphism; [apply H.(err_eequiv) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv) |].
  reflexivity.
Qed.

Lemma neg_sem_nrm_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  neg_sem_nrm ⟦ e1 ⟧.(nrm) ⊆
  neg_sem_nrm ⟦ e2 ⟧.(nrm) ∪
  ((⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm)) × int64).
Proof.
  unfold neg_sem_nrm, neg_sem_err; sets_unfold.
  intros ? ? ? s i.
  intros [i1 [? ?] ].
  apply H.(nrm_erefine) in H0.
  sets_unfold in H0.
  destruct H0; [| tauto].
  left; exists i1.
  tauto.
Qed.

Lemma neg_sem_err_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  ⟦ e1 ⟧.(err) ∪ neg_sem_err ⟦ e1 ⟧.(nrm) ⊆
  ⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm).
Proof.
  unfold neg_sem_err; sets_unfold.
  intros ? ? ? s ?.
  destruct H0; [apply H.(err_erefine) in H0; tauto |].
  destruct H0 as [i1 [? ?] ].
  apply H.(nrm_erefine) in H0.
  sets_unfold in H0.
  destruct H0; [| tauto].
  right; exists i1.
  tauto.
Qed.

Instance EUnop_congr: forall op, (** 一元运算符保持等价关系*)
  Proper (eequiv ==> eequiv) (EUnop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  + split.
    - apply not_sem_nrm_congr; tauto.
    - simpl. apply not_sem_err_congr; tauto.
  + split.
    - apply neg_sem_nrm_congr; tauto.
    - apply neg_sem_err_congr; tauto.
Qed.

Instance EUnop_mono: forall op, (** 一元运算符保持精化关系*)
  Proper (erefine ==> erefine) (EUnop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  + split.
    - simpl. apply not_sem_nrm_mono; tauto.
    - simpl. apply not_sem_err_mono; tauto.
  + split.
    - apply neg_sem_nrm_mono; tauto.
    - apply neg_sem_err_mono; tauto.
Qed.

(** 下面证明程序语句中的语法连接词也能保持语义等价性和精化关系。顺序执行保持等价
    性是比较显然的。*)

Instance CSeq_congr:
  Proper (cequiv ==> cequiv ==> cequiv) CSeq.
Proof.
  unfold Proper, respectful.
  intros c11 c12 ? c21 c22 ?.
  split; simpl.
  + rewrite H.(nrm_cequiv).
    rewrite H0.(nrm_cequiv).
    reflexivity.
  + rewrite H.(nrm_cequiv).
    rewrite H.(err_cequiv).
    rewrite H0.(err_cequiv).
    reflexivity.
  + rewrite H.(nrm_cequiv).
    rewrite H.(inf_cequiv).
    rewrite H0.(inf_cequiv).
    reflexivity.
Qed.

(** 为了证明顺序执行能保持精化关系，先证明两条引理。*)

Lemma Rels_times_full_concat2:
  forall {A B C: Type} (X: A -> Prop) (Y: B -> C -> Prop),
    (X × B) ∘ Y ⊆ X × C.
Proof.
  intros.
  sets_unfold.
  intros a c.
  intros [b [? ?] ].
  tauto.
Qed.

Lemma Rels_times_full_concat1:
  forall {A B: Type} (X: A -> Prop) (Y: B -> Prop),
    (X × B) ∘ Y ⊆ X.
Proof.
  intros.
  sets_unfold.
  intros a.
  intros [b [? ?] ].
  tauto.
Qed.

(** 下面证明顺序执行能保持精化关系。*)

Instance CSeq_mono:
  Proper (crefine ==> crefine ==> crefine) CSeq.
Proof.
  unfold Proper, respectful.
  intros c11 c12 ? c21 c22 ?.
  split; simpl.
  + rewrite H.(nrm_crefine).
    rewrite H0.(nrm_crefine).
    rewrite Rels_concat_union_distr_l.
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_times_full_concat2. (**  ⟦ c12 ⟧.(err) × state ∘ ⟦ c22 ⟧.(err) × state) 属于  ⟦ c12 ⟧.(err) × state*)
    sets_unfold; intros s1 s2; tauto.
  + rewrite H.(err_crefine). (**出错的情况*)
    rewrite H.(nrm_crefine).
    rewrite H0.(err_crefine).
    rewrite Rels_concat_union_distr_r.
    rewrite Rels_times_full_concat1.
    sets_unfold; intros s; tauto.
  + rewrite H.(inf_crefine). (**无穷的情况*)
    rewrite H0.(inf_crefine).
    rewrite H.(nrm_crefine).
    rewrite Rels_concat_union_distr_l.
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_times_full_concat1.
    sets_unfold; intros s; tauto.
Qed.

(** 为了证明if语句能保持语义等价关系与精化关系，先证明_[test_true]_与
    _[test_false]_的性质。*)

Lemma test_true_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  test_true ⟦ e1 ⟧ ⊆
  test_true ⟦ e2 ⟧ ∪ (⟦ e2 ⟧.(err) × state).
Proof.
  intros.
  unfold test_true; sets_unfold; intros s1 s2.
  intros [ [i [? ?] ] ?].
  apply H.(nrm_erefine) in H0.
  sets_unfold in H0.
  destruct H0; [| tauto].
  left; split; [| tauto].
  exists i; tauto.
Qed.

Lemma test_false_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  test_false ⟦ e1 ⟧ ⊆
  test_false ⟦ e2 ⟧ ∪ (⟦ e2 ⟧.(err) × state).
Proof.
  intros.
  unfold test_false; sets_unfold; intros s1 s2.
  intros [? ?].
  apply H.(nrm_erefine) in H0.
  sets_unfold in H0.
  destruct H0; [| tauto].
  tauto.
Qed.

Lemma test_true_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  test_true ⟦ e1 ⟧ == test_true ⟦ e2 ⟧.
Proof.
  intros.
  unfold test_true; sets_unfold; intros s1 s2.
  apply and_iff_morphism; [| reflexivity].
  apply ex_iff_morphism; intros i.
  apply and_iff_morphism; [| reflexivity].
  apply H.(nrm_eequiv).
Qed.

Lemma test_false_congr: forall (e1 e2: expr),
  e1 ~=~ e2 ->
  test_false ⟦ e1 ⟧ == test_false ⟦ e2 ⟧.
Proof.
  intros.
  unfold test_false; sets_unfold; intros s1 s2.
  apply and_iff_morphism; [| reflexivity].
  apply H.(nrm_eequiv).
Qed.

(** 基于此就可以证明if语句能保持语义等价关系与精化关系。*)

Instance CIf_congr:
  Proper (eequiv ==> cequiv ==> cequiv ==> cequiv) CIf.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c11 c12 ? c21 c22 ?.
  split; simpl.
  + rewrite (test_true_congr _ _ H).
    rewrite (test_false_congr _ _ H).
    rewrite H0.(nrm_cequiv).
    rewrite H1.(nrm_cequiv).
    reflexivity.
  + rewrite (test_true_congr _ _ H).
    rewrite (test_false_congr _ _ H).
    rewrite H.(err_eequiv).
    rewrite H0.(err_cequiv).
    rewrite H1.(err_cequiv).
    reflexivity.
  + rewrite (test_true_congr _ _ H).
    rewrite (test_false_congr _ _ H).
    rewrite H0.(inf_cequiv).
    rewrite H1.(inf_cequiv).
    reflexivity.
Qed.

Instance CIf_mono:
  Proper (erefine ==> crefine ==> crefine ==> crefine) CIf.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c11 c12 ? c21 c22 ?.
  split; simpl.
  + rewrite (test_true_mono e1 e2 H).
    rewrite (test_false_mono e1 e2 H).
    rewrite H0.(nrm_crefine), H1.(nrm_crefine).
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite ! Rels_times_full_concat2.
    sets_unfold; intros s1 s2; tauto.
  + rewrite (test_true_mono e1 e2 H).
    rewrite (test_false_mono e1 e2 H).
    rewrite H.(err_erefine).
    rewrite H0.(err_crefine), H1.(err_crefine).
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_times_full_concat1.
    sets_unfold; intros s; tauto.
  + rewrite (test_true_mono e1 e2 H).
    rewrite (test_false_mono e1 e2 H).
    rewrite H0.(inf_crefine), H1.(inf_crefine).
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite ! Rels_times_full_concat1.
    sets_unfold; intros s; tauto.
Qed.

(** 要证明while语句保持语义等价关系，就需要运用集合并集的有关性质，还需要对迭代
    的次数进行归纳。*)

Instance CWhile_congr:
  Proper (eequiv ==> cequiv ==> cequiv) CWhile.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c1 c2 ?.
  split; simpl.
  (** 正常运行终止的情况。*)
  + apply Sets_indexed_union_congr; intros n.
    induction n; simpl.
    - reflexivity.
    - rewrite IHn.
      rewrite (test_true_congr _ _ H).
      rewrite (test_false_congr _ _ H).
      rewrite H0.(nrm_cequiv).
      reflexivity.
  (** 运行出错的情况。*)
  + apply Sets_indexed_union_congr; intros n.
    induction n; simpl.
    - reflexivity.
    - rewrite IHn.
      rewrite (test_true_congr _ _ H).
      rewrite H.(err_eequiv).
      rewrite H0.(nrm_cequiv).
      rewrite H0.(err_cequiv).
      reflexivity.
  (** 运行不终止的情况。*)
  + apply Sets_general_union_congr.
    intros X.
    unfold_CL_defs.
    rewrite H0.(nrm_cequiv).
    rewrite H0.(inf_cequiv).
    rewrite (test_true_congr _ _ H).
    reflexivity.
Qed.

(** 要证明while语句保持精化关系就更复杂一些了。*)

Definition boundedLB_nrm
             (D0: EDenote)
             (D1: CDenote)
             (n: nat):
  state -> state -> Prop :=
  Nat.iter
    n
    (fun X => test_true D0 ∘ D1.(nrm) ∘ X ∪ test_false D0)
    ∅.

Definition boundedLB_err
             (D0: EDenote)
             (D1: CDenote)
             (n: nat):
  state -> Prop :=
  Nat.iter
    n
    (fun X => test_true D0 ∘ D1.(nrm) ∘ X ∪ test_true D0 ∘ D1.(err) ∪ D0.(err))
    ∅.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ D1.(nrm) ∘ X ∪
      test_true D0 ∘ D1.(inf).

Lemma boundedLB_nrm_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    boundedLB_nrm ⟦ e1 ⟧ ⟦ c1 ⟧ n ⊆
    boundedLB_nrm ⟦ e2 ⟧ ⟦ c2 ⟧ n ∪
    (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧ n × state).
Proof.
  intros.
  induction n; simpl.
  + apply Sets_empty_included.
  + rewrite IHn.
    rewrite (test_true_mono _ _ H).
    rewrite (test_false_mono _ _ H).
    rewrite H0.(nrm_crefine).
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite ! Rels_times_full_concat2.
    sets_unfold; intros s1 s2; tauto.
Qed.

Lemma boundedLB_err_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    boundedLB_err ⟦ e1 ⟧ ⟦ c1 ⟧ n ⊆
    boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧ n.
Proof.
  intros.
  induction n; simpl.
  + apply Sets_empty_included.
  + rewrite IHn.
    rewrite (test_true_mono _ _ H).
    rewrite H.(err_erefine).
    rewrite H0.(nrm_crefine).
    rewrite H0.(err_crefine).
    rewrite ! Rels_concat_union_distr_r.
    rewrite ! Rels_concat_union_distr_l.
    rewrite ! Rels_times_full_concat1.
    sets_unfold; intros s; tauto.
Qed.

Lemma Sets_complement_indexed_union:
  forall {A I: Type} (Xs: I -> A -> Prop),
    Sets.complement (⋃ Xs) ==
    ⋂ (fun n => Sets.complement (Xs n)).
Proof.
  intros.
  sets_unfold.
  split.
  + apply not_ex_all_not.
  + apply all_not_not_ex.
Qed.

Definition noerrorLB (D1: EDenote) (D2: CDenote): state -> Prop :=
  Sets.complement (⋃ (boundedLB_err D1 D2)).

Lemma iter_err_fact:
  forall (D1: EDenote) (D2: CDenote),
    test_true D1 ∘ D2.(nrm) ∘ ⋃ (boundedLB_err D1 D2) ⊆
    ⋃ (boundedLB_err D1 D2).
Proof.
  intros.
  rewrite ! Rels_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros n.
  rewrite <- (Sets_included_indexed_union _ _ (S n)).
  simpl.
  sets_unfold; intros s; tauto.
Qed.

Lemma Rels_concat_excluding_r:
  forall
    {A B: Type}
    (R: A -> B -> Prop)
    (S T: B -> Prop),
    (R ∘ S) ∩ Sets.complement (R ∘ T) ⊆
    R ∘ (S ∩ Sets.complement T).
Proof.
  intros.
  Sets_unfold; intros a.
  intros [ [b [? ?] ] ?].
  exists b.
  split; [tauto |].
  split; [tauto |].
  assert (T b -> exists b : B, R a b /\ T b); [| tauto].
  clear H1; intros.
  exists b; tauto.
Qed.

Lemma noerrorLB_fact1:
  forall (D1: EDenote) (D2: CDenote),
    D1.(err) ∩ noerrorLB D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorLB.
  rewrite Sets_complement_indexed_union.
  apply Sets_equiv_Sets_included.
  split; [| apply Sets_empty_included].
  rewrite (Sets_indexed_intersect_included _ _ (S O)).
  simpl.
  sets_unfold; intros s.
  tauto.
Qed.

Lemma noerrorLB_fact2:
  forall (D1: EDenote) (D2: CDenote),
    (test_true D1 ∘ D2.(err)) ∩ noerrorLB D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorLB.
  rewrite Sets_complement_indexed_union.
  apply Sets_equiv_Sets_included.
  split; [| apply Sets_empty_included].
  rewrite (Sets_indexed_intersect_included _ _ (S O)).
  simpl.
  sets_unfold; intros s.
  tauto.
Qed.

Lemma inf_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) X,
    e1 <<= e2 ->
    c1 <<= c2 ->
    is_inf ⟦ e1 ⟧ ⟦ c1 ⟧ X ->
    is_inf ⟦ e2 ⟧ ⟦ c2 ⟧ (X ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧). (**x集合中会执行while e2 do c2出错的情况排除*)
Proof.
  unfold is_inf.
  intros.
  rewrite H1 at 1.
  rewrite (test_true_mono _ _ H).
  rewrite H0.(nrm_crefine).
  rewrite H0.(inf_crefine).
  rewrite ! Rels_concat_union_distr_r.
  rewrite ! Rels_concat_union_distr_l.
  rewrite ! Rels_times_full_concat1.
  rewrite ! Sets_intersect_union_distr_r. (**交集对于bingji的分配律*)
  rewrite noerrorLB_fact1.
  rewrite noerrorLB_fact2.
  rewrite ! Sets_union_empty.
  unfold noerrorLB at 1.
  rewrite <- iter_err_fact at 1.
  rewrite ! Rels_concat_excluding_r.
  fold (noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧).
  sets_unfold; intros s; tauto.
Qed.

Instance CWhile_mono:
  Proper (erefine ==> crefine ==> crefine) CWhile.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c1 c2 ?.
  split; simpl.
  + apply Sets_indexed_union_included; intros n. (**无穷并的每一项都是有*)
    unfold BW_LFix. unfold_CPO_defs.
    rewrite <- ! (Sets_included_indexed_union _ _ n).
    apply boundedLB_nrm_mono_aux; tauto.
  + apply Sets_indexed_union_included; intros n.
    unfold BW_LFix. unfold_CPO_defs.
    rewrite <- (Sets_included_indexed_union _ _ n).
    apply boundedLB_err_mono_aux; tauto.
  + apply Sets_general_union_included. unfold_CL_defs.
    intros X ?.
    pose proof inf_mono_aux _ _ _ _ _ H H0 H1.
    unfold KT_GFix; unfold_CL_defs.
    rewrite <- (Sets_included_general_union _ (X ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧))
      by (exact H2).
    unfold noerrorLB.
    sets_unfold; intros s; tauto.
Qed.

(** 下面是一个证明中使用了语义等价的重要性质：语义等价是等价关系、语法连接词保持等价性。*)

Example cequiv_sample: forall (e: expr) (c1 c2 c3 c4: com),
  [[ if (e) then { c1 } else { c2 }; c3; c4 ]] ~=~
  [[ if (e) then { c1; c3 } else { c2; c3 }; c4 ]].
Proof.
  intros.
  rewrite CSeq_assoc.
  rewrite CIf_CSeq.
  reflexivity.
Qed.

