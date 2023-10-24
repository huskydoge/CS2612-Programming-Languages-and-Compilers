Require Import Coq.Arith.PeanoNat.

(** 在Coq中，许多数学上的集合可以用归纳类型定义。例如，Coq中自然数的定义就是最简
    单的归纳类型之一。  

    下面Coq代码可以用于查看_[nat]_在Coq中的定义。*)
Print nat.
(** 查询结果如下。  
    Inductive nat := O : nat | S: nat -> nat.   

    可以看到，自然数集合的归纳定义可以看做_[list]_进一步退化的结果。下面我们在
    Coq中定义自然数的加法，并且也试着证明一条基本性质：加法交换律。  


    由于Coq的标准库中已经定义了自然数以及自然数的加法。我们开辟一个_[NatDemo]_来
    开发我们自己的定义与证明。以免与Coq标准库的定义相混淆。*)

Module NatDemo.

(** 先定义自然数_[nat]_。*)

Inductive nat :=
| O: nat
| S (n: nat): nat.

(** 再定义自然数加法。*)

Fixpoint add (n m: nat): nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** 下面证明加法交换律。*)

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n.
  (** 证明到此处，我们发现我们需要首先证明_[n + 0 = n]_这条性质，我们先终止交换
      律的证明，而先证明这条引理。*)
Abort.

Lemma add_0_r: forall n, add n O = n.
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n; simpl.
  + rewrite add_0_r.
    reflexivity.
  + (** 证明到此处，我们发现我们需要还需要证明关于_[m + (S n)]_相关的性质。*)
Abort.

Lemma add_succ_r: forall n m,
  add n (S m) = S (add n m).
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

(** 现在已经可以在Coq中完成加法交换律的证明了。*)

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n; simpl.
  + rewrite add_0_r.
    reflexivity.
  + rewrite add_succ_r.
    rewrite IHn.
    reflexivity.
Qed.

(** 由于自然数范围内，数学意义上的减法是一个部分函数，因此，相关定义在Coq中并不常用。相
    对而言，自然数的加法与乘法在Coq中更常用。*)

Fixpoint mul (n m: nat): nat :=
  match n with
  | O => O
  | S p => add m (mul p m)
  end.

(** 下面列举加法与乘法的其它重要性质。*)

Theorem add_assoc:
  forall n m p, add n (add m p) = add (add n m) p.
Proof.
  intros n m p; induction n; simpl.
  + reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_cancel_l:
  forall n m p, add p n = add p m <-> n = m.
Proof.
  intros n m p; split.
  + induction p; simpl; intros H.
    - tauto.
    - injection H as H.
      pose proof IHp H.
      tauto.
  + intros H.
    rewrite H.
    reflexivity.
Qed.

Theorem add_cancel_r:
  forall n m p, add n p = add m p <-> n = m.
Proof.
  intros n m p.
  rewrite (add_comm n p), (add_comm m p).
  apply add_cancel_l.
Qed.

Lemma mul_0_r: forall n, mul n O = O.
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + apply IHn.
Qed.

Lemma mul_succ_r:
  forall n m, mul n (S m) = add (mul n m) n.
Proof.
  intros n m; induction n; simpl.
  + reflexivity.
  + rewrite IHn, add_succ_r.
    rewrite <- add_assoc.
    reflexivity.
Qed.

Theorem mul_comm:
  forall n m, mul n m = mul m n.
Proof.
  intros n m; induction n; simpl.
  + rewrite mul_0_r.
    reflexivity.
  + rewrite mul_succ_r.
    rewrite IHn, add_comm.
    reflexivity.
Qed.

Theorem mul_add_distr_r:
  forall n m p, mul (add n m) p = add (mul n p) (mul m p).
Proof.
  intros n m p; induction n; simpl.
  - reflexivity.
  - rewrite <- add_assoc, IHn.
    reflexivity.
Qed.

Theorem mul_add_distr_l:
  forall n m p, mul n (add m p) = add (mul n m) (mul n p).
Proof.
  intros n m p.
  rewrite (mul_comm n (add m p)), (mul_comm n m), (mul_comm n p).
  apply mul_add_distr_r.
Qed.

Theorem mul_assoc:
  forall n m p, mul n (mul m p) = mul (mul n m) p.
Proof.
  intros n m p; induction n; simpl.
  + reflexivity.
  + rewrite IHn, mul_add_distr_r.
    reflexivity.
Qed.

Theorem mul_1_l : forall n, mul (S O) n = n.
Proof. intros. simpl. apply add_0_r. Qed.

Theorem mul_1_r : forall n, mul n (S O) = n.
Proof. intros. rewrite mul_comm, mul_1_l. reflexivity. Qed.

End NatDemo.

(** 上面介绍的加法与乘法运算性质在Coq标准库中已有证明，其定理名称如下。*)

Check Nat.add_comm.
Check Nat.add_assoc.
Check Nat.add_cancel_l.
Check Nat.add_cancel_r.
Check Nat.mul_comm.
Check Nat.mul_add_distr_r.
Check Nat.mul_add_distr_l.
Check Nat.mul_assoc.
Check Nat.mul_1_l.
Check Nat.mul_1_r.

(** 前面已经提到，Coq在自然数集合上不便于表达减法等运算，因此，Coq用户有些时候可以选用
    _[Z]_而非_[nat]_。然而，由于其便于表示计数概念以及表述数学归纳法，_[nat]_依然有许
    多用途。例如，Coq标准库中的_[Nat.iter]_就表示函数多次迭代，具体而言，
    _[Nat.iter n f]_表示将函数_[f]_迭代_[n]_次的结果。其Coq定义如下：  

    Fixpoint iter {A: Type} (n: nat) (f: A -> A) (x: A): A :=
      match n with
      | O => x
      | S n' => f (iter n' f x)
      end.   

    它符合许多重要性质，例如：*)

Theorem iter_S: forall {A: Type} (n: nat) (f: A -> A) (x: A),
  Nat.iter n f (f x) = Nat.iter (S n) f x.

(** 注意，哪怕是如此简单的性质，我们还是需要在Coq中使用归纳法证明。*)

Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn; simpl.
    reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)

Theorem iter_add: forall {A: Type} (n m: nat) (f: A -> A) (x: A),
  Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)

Theorem iter_mul: forall {A: Type} (n m: nat) (f: A -> A) (x: A),
  Nat.iter (n * m) f x = Nat.iter n (Nat.iter m f) x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


