Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.SyntaxInCoq.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 简单表达式的指称语义 *)

Module DntSem_SimpleWhile1.
Import Lang_SimpleWhile.



(** 指称语义是一种定义程序行为的方式。在极简的SimpleWhile语言中，整数类型表达式
    中只有整数常量、变量、加法、减法与乘法运算。  

    我们约定其中整数变量的值、整数运算的结果都是没有范围限制的。基于这一约定，我
    们可以如下定义表达式_[e]_在程序状态_[st]_上的值。

    首先定义程序状态集合：*)

Definition state: Type := var_name -> Z.

(** 下面使用Coq递归函数定义整数类型表达式的行为。*)

Fixpoint eval_expr_int (e: expr_int) (s: state) : Z :=
  match e with
  | EConst n => n
  | EVar X => s X
  | EAdd e1 e2 => eval_expr_int e1 s + eval_expr_int e2 s
  | ESub e1 e2 => eval_expr_int e1 s - eval_expr_int e2 s
  | EMul e1 e2 => eval_expr_int e1 s * eval_expr_int e2 s
  end.

(** 下面是两个具体的例子。*)

Example eval_example1: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  eval_expr_int [["x" + "y"]] s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Example eval_example2: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  eval_expr_int [["x" * "y" + 1]] s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.






(** * 行为等价 *)

(** 基于整数类型表达式的语义定义_[eval_expr_int]_，我们可以定义整数类型表达式之
    间的行为等价（亦称语义等价）：两个表达式_[e1]_与_[e2]_是等价的当且仅当它们在
    任何程序状态上的求值结果都相同。*)

Definition expr_int_equiv (e1 e2: expr_int): Prop :=
  forall st, eval_expr_int e1 st = eval_expr_int e2 st.

Notation "e1 '~=~' e2" := (expr_int_equiv e1 e2)
  (at level 69, no associativity).

(** 下面是一些表达式语义等价的例子。 *)

Example expr_int_equiv_sample:
  [["x" + "x"]] ~=~ [["x" * 2]].
Proof.
  intros.
  unfold expr_int_equiv.
  (** 上面的_[unfold]_指令表示展开一项定义，一般用于非递归的定义。*)
  intros.
  simpl.
  lia.
Qed.

Lemma zero_plus_equiv: forall (a: expr_int),
  [[0 + a]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: expr_int),
  [[a + 0]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: expr_int),
  [[a - 0]] ~=~ a.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: expr_int),
  [[0 * a]] ~=~ 0.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: expr_int),
  [[a * 0]] ~=~ 0.
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  [[EConst n + EConst m]] ~=~ EConst (n + m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_minus_const: forall n m: Z,
  [[EConst n - EConst m]] ~=~ EConst (n - m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_mult_const: forall n m: Z,
  [[EConst n * EConst m]] ~=~ EConst (n * m).
Proof.
  intros.
  unfold expr_int_equiv.
  intros.
  simpl.
  reflexivity.
Qed.

(** 下面定义一种简单的语法变换---常量折叠---并证明其保持语义等价性。所谓常量折叠
    指的是将只包含常量而不包含变量的表达式替换成为这个表达式的值。*)

Fixpoint fold_constants (e : expr_int) : expr_int :=
  match e with
  | EConst n    => EConst n
  | EVar x      => EVar x
  | EAdd e1 e2  =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 + n2)
      | _, _ => EAdd (fold_constants e1) (fold_constants e2)
      end
  | ESub e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 - n2)
      | _, _ => ESub (fold_constants e1) (fold_constants e2)
    end
  | EMul e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 * n2)
      | _, _ => EMul (fold_constants e1) (fold_constants e2)
    end
  end.

(** 这里我们可以看到，Coq中_[match]_的使用是非常灵活的。(1) 我们不仅可以对一个变
    量的值做分类讨论，还可以对一个复杂的Coq式子的取值做分类讨论；(2) 我们可以对
    多个值同时做分类讨论；(3) 我们可以用下划线表示_[match]_的缺省情况。下面是两
    个例子：*)

Example fold_constants_ex1:
    fold_constants [[(1 + 2) * "k"]] = [[3 * "k"]].
Proof. intros. reflexivity. Qed.

(** 注意，根据我们的定义，_[fold_constants]_并不会将_[0 + "y"]_中的_[0]_消去。*)

Example fold_expr_int_ex2 :
  fold_constants [["x" - ((0 * 6) + "y")]] = [["x" - (0 + "y")]].
Proof. intros. reflexivity. Qed.

(** 下面我们在Coq中证明，_[fold_constants]_保持表达式行为不变。 *)

Theorem fold_constants_sound : forall a,
  fold_constants a ~=~ a.
Proof.
  unfold expr_int_equiv. intros.
  induction a.
  (** 常量的情况 *)
  + simpl.
    reflexivity.
  (** 变量的情况 *)
  + simpl.
    reflexivity.
  (** 加号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  (** 减号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  (** 乘号的情况 *)
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
Qed.

End DntSem_SimpleWhile1.

(** * 利用高阶函数定义指称语义 *)

Module DntSem_SimpleWhile2.
Import Lang_SimpleWhile.

Definition state: Type := var_name -> Z.

Definition add_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s + D2 s.

Definition sub_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s - D2 s.

Definition mul_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s * D2 s.

(** 下面是用于类型查询的_[Check]_指令。*)

Check add_sem.

(** 可以看到_[add_sem]_的类型是_[(state -> Z) -> (state -> Z) -> state -> Z]_，
    这既可以被看做一个三元函数，也可以被看做一个二元函数，即函数之间的二元函数。  

    基于上面高阶函数，可以重新定义表达式的指称语义。*)

Definition const_sem (n: Z) (s: state): Z := n.
Definition var_sem (X: var_name) (s: state): Z := s X.

Fixpoint eval_expr_int (e: expr_int): state -> Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

End DntSem_SimpleWhile2.

(** * 布尔表达式语义 *)

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile DntSem_SimpleWhile2.

(** 在Coq中可以如下定义：*)

Definition true_sem (s: state): bool := true.

Definition false_sem (s: state): bool := false.

Definition lt_sem (D1 D2: state -> Z) s: bool :=
  Z.ltb (D1 s) (D2 s).

Definition and_sem (D1 D2: state -> bool) s: bool :=
  andb (D1 s) (D2 s).

Definition not_sem (D: state -> bool) s: bool :=
  negb (D s).

Fixpoint eval_expr_bool (e: expr_bool): state -> bool :=
  match e with
  | ETrue =>
      true_sem
  | EFalse =>
      false_sem
  | ELt e1 e2 =>
      lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 =>
      and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 =>
      not_sem (eval_expr_bool e1)
  end.

End DntSem_SimpleWhile3.




(** * Coq中的集合与关系 *)


(** 本课程提供的SetsClass库中提供了有关集合的一系列定义。例如：

    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 一列集合的并：用_[⋃]_表示，定义为_[Sets.indexed_union]_；

    - 一列集合的交：用_[⋂]_表示，定义为_[Sets.indexed_intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_；

    - 二元关系的连接：用_[∘]_表示，定义为_[Rels.concat]_；

    - 等同关系：定义为_[Rels.id]_；

    - 测试关系：定义为_[Rels.test]_。

    在CoqIDE中，你可以利用CoqIDE对于unicode的支持打出特殊字符：

    - 首先，在打出特殊字符的latex表示法；

    - 再按shift+空格键；

    - latex表示法就自动转化为了相应的特殊字符。

    例如，如果你需要打出符号_[∈]_，请先在输入框中输入_[\in]_，当光标紧跟在_[n]_
    这个字符之后的时候，按shift+空格键即可。例如，下面是两个关于集合的命题：*)

Check forall A (X: A -> Prop), X ∪ ∅ == X.

Check forall A B (X Y: A -> B -> Prop), X ∪ Y ⊆ X.

(** 由于集合以及集合间的运算是基于Coq中的命题进行定义的，集合相关性质的证明也可
    以规约为与命题有关的逻辑证明。例如，我们想要证明，交集运算具有交换律：*)

Lemma Sets_intersect_comm: forall A (X Y: A -> Prop),
  X ∩ Y == Y ∩ X.
Proof.
  intros.
  (** 下面一条命令_[Sets_unfold]_是SetsClass库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  Sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : A, a ∈ X /\ a ∈ Y <-> a ∈ Y /\ a ∈ X]_
      这个关于逻辑的命题在Coq中是容易证明的。*)
  intros.
  tauto.
Qed.

(** 下面是一条关于并集运算的性质。*)

Lemma Sets_included_union1: forall A (X Y: A -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  Sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : A, a ∈ X -> a ∈ X \/ a ∈ Y]_。*)
  intros.
  tauto.
Qed.

(************)
(** 习题：  *)
(************)


(** 下面是一条关于二元关系复合的性质。转化后得到的命题要复杂一些，请在Coq中证明这个关于
    逻辑的命题。*)

Lemma Rels_concat_assoc: forall A (X Y Z: A -> A -> Prop),
  (X ∘ Y) ∘ Z == X ∘ (Y ∘ Z).
Proof.
  intros.
  Sets_unfold.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** SetsClass库中提供了一系列有关集合运算的性质的证明。未来大家在证明中既可以使用
    _[Sets_unfold]_将关于集合运算的命题转化为关于逻辑的命题，也可以直接使用下面这些性
    质完成证明。  

      Sets_equiv_Sets_included:
    forall x y, x == y <-> x ⊆ y /\ y ⊆ x;
  Sets_empty_included:
    forall x, ∅ ⊆ x;
  Sets_included_full:
    forall x, x ⊆ Sets.full;
  Sets_intersect_included1:
    forall x y, x ∩ y ⊆ x;
  Sets_intersect_included2:
    forall x y, x ∩ y ⊆ y;
  Sets_included_intersect:
    forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z;
  Sets_included_union1:
    forall x y, x ⊆ x ∪ y;
  Sets_included_union2:
    forall x y, y ⊆ x ∪ y;
  Sets_union_included_strong2:
    forall x y z u,
       x ∩ u ⊆ z -> y ∩ u ⊆ z -> (x ∪ y) ∩ u ⊆ z;
  
      Sets_included_indexed_union:
    forall xs n, xs n ⊆ ⋃ xs;
  Sets_indexed_union_included:
    forall xs y, (forall n, xs n ⊆ y) -> ⋃ xs ⊆ y;
  Sets_indexed_intersect_included:
    forall xs n, ⋂ xs ⊆ xs n;
  Sets_included_indexed_intersect:
    forall xs y, (forall n : nat, y ⊆ xs n) -> y ⊆ ⋂ xs;
  
      Rels_concat_union_distr_r:
    forall x1 x2 y,
      (x1 ∪ x2) ∘ y == (x1 ∘ y) ∪ (x2 ∘ y);
  Rels_concat_union_distr_l:
    forall x y1 y2,
      x ∘ (y1 ∪ y2) == (x ∘ y1) ∪ (x ∘ y2);
  Rels_concat_mono:
    forall x1 x2,
      x1 ⊆ x2 ->
      forall y1 y2,
        y1 ⊆ y2 ->
        x1 ∘ y1 ⊆ x2 ∘ y2;
  Rels_concat_assoc:
    forall x y z,
      (x ∘ y) ∘ z == x ∘ (y ∘ z);
  Rels_concat_id_l:
    forall x, Rels.id ∘ x == x;
  Rels_concat_id_r:
    forall x, x ∘ Rels.id == x;  

    由于上面提到的集合与关系运算都能保持集合相等，也都能保持集合包含关系，因此
    SetsClass库支持其用户使用_[rewrite]_指令处理集合之间的相等关系与包含关系。下面是
    两个典型的例子*)

Fact sets_ex1:
  forall (A: Type) (R1 R2 R3 R4: A -> A -> Prop),
    R1 ∘ (R2 ∘ (R3 ∘ R4)) == ((R1 ∘ R2) ∘ R3) ∘ R4.
Proof.
  intros.
  rewrite Rels_concat_assoc.
  rewrite Rels_concat_assoc.
  reflexivity.
Qed.

Fact sets_ex2:
  forall (A: Type) (R1 R2 R3 R4: A -> A -> Prop),
    R1 ⊆ R2 ->
    R1 ∘ R3 ∪ R4 ⊆ R2 ∘ R3 ∪ R4.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** * 在Coq中定义程序语句的语义 *)

Module DntSem_SimpleWhile4.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3.

(** 下面在Coq中写出程序语句的指称语义。*)

Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition asgn_sem
             (X: var_name)
             (D: state -> Z)
             (st1 st2: state): Prop :=
  st2 X = D st1 /\
  forall Y, X <> Y -> st2 Y = st1 Y.

Definition seq_sem
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun st => D st = true).

Definition test_false
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun st => D st = false).

Definition if_sem
             (D0: state -> bool)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint iterLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | S n0 => test_true D0 ∘ D1 ∘ iterLB D0 D1 n0
  end.

Module WhileSem1.

Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iterLB D0 D1).

End WhileSem1.

Fixpoint boundedLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ boundedLB D0 D1 n0) ∪
      (test_false D0)
  end.

Module WhileSem2.

Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (boundedLB D0 D1).

End WhileSem2.

(** 我们选择第二种定义。*)

Export WhileSem2.

(** 下面是程序语句指称语义的递归定义。*)

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  end.

(** 基于上面定义，可以证明一些简单的程序性质。*)

Example inc_x_fact: forall s1 s2 n,
  eval_com (CAsgn "x" [["x" + 1]]) s1 s2 ->
  s1 "x" = n ->
  s2 "x" = n + 1.
Proof.
  intros.
  simpl in H.
  unfold asgn_sem, add_sem, var_sem, const_sem in H.
  lia.
Qed.

(** 更多关于程序行为的有用性质可以使用集合与关系的运算性质完成证明。*)

Lemma seq_skip: forall c,
  eval_com (CSeq c CSkip) == eval_com c.
Proof.
  intros.
  simpl.
  unfold seq_sem, skip_sem.
  apply Rels_concat_id_r.
Qed.

Lemma skip_seq: forall c,
  eval_com (CSeq CSkip c) == eval_com c.
Proof.
  intros.
  simpl.
  unfold seq_sem, skip_sem.
  apply Rels_concat_id_l.
Qed.

Lemma seq_assoc: forall c1 c2 c3,
  eval_com (CSeq (CSeq c1 c2) c3) ==
  eval_com (CSeq c1 (CSeq c2 c3)).
Proof.
  intros.
  simpl.
  unfold seq_sem.
  apply Rels_concat_assoc.
Qed.

Lemma while_sem_congr2: forall D1 D2 D2',
  D2 == D2' ->
  while_sem D1 D2 == while_sem D1 D2'.
Proof.
  intros.
  unfold while_sem.
  apply Sets_indexed_union_congr.
  intros n.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    rewrite H.
    reflexivity.
Qed.

(** 下面我们证明，我们先前定义的_[remove_skip]_变换保持程序行为不变。*)

Import LangTrans.

Lemma remove_skip_sound: forall c,
  eval_com (remove_skip c) == eval_com c.
Proof.
  intros.
  induction c; simpl.
  + reflexivity.
  + reflexivity.
  + unfold seq_sem.
    rewrite <- IHc1, <- IHc2.
    destruct (remove_skip c1), (remove_skip c2);
      simpl; unfold skip_sem, seq_sem;
      rewrite ? Rels_concat_id_l, ? Rels_concat_id_r;
      reflexivity.
  + unfold if_sem.
    rewrite IHc1, IHc2.
    reflexivity.
  + apply while_sem_congr2.
    apply IHc.
Qed.

End DntSem_SimpleWhile4.

