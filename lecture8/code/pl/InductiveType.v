Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.CoqIntro.
Local Open Scope Z.

(** * 关于等式的证明 *)


(** 在先前证明单调函数性质的过程中，我们经常会要通过参数之间的大小关系推导出函数值之间
    的大小关系。例如，当_[f]_是一个单调函数时，可以由_[x <= y]_推出_[f x <= f y]_。
    对于一般的函数，我们也可以由参数相等，推出函数值相等，即由_[x = y]_推出
    _[f x = f y]_。下面的证明中就要用到这一性质。
*)

Definition is_fixpoint (f: Z -> Z) (x: Z): Prop :=
  f x = x.

Theorem fixpoint_self_comp: forall f x,
  is_fixpoint f x ->
  is_fixpoint (Zcomp f f) x.
Proof.
  unfold is_fixpoint, Zcomp.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(** 在数学上，如果_[f x = x]_，那么我们就称_[x]_是函数_[f]_的一个不动点。上面的定理证
    明了，如果_[x]_是_[f]_的不动点，那么_[x]_也是_[f]_与自身复合结果的不动点。在这一
    证明中，前提_[H]_是命题_[f x = x]_。证明指令_[rewrite H]_的效果是将结论中的
    _[f x]_替换为_[x]_，因此，第一次使用该指令后，原先需要证明的_[f (f x) = x]_规约
    为了_[f x = x]_。这一步背后的证明实际就用到了“只要函数_[f]_的参数不变，那么函数值
    也不变”这条性质。  

        下面关于不动点简单性质的证明需要我们灵活使用rewrite指令。*)

Example fixpoint_self_comp23: forall f x,
  is_fixpoint (Zcomp f f) x ->
  is_fixpoint (Zcomp f (Zcomp f f)) x ->
  is_fixpoint f x.
Proof.
  unfold is_fixpoint, Zcomp.
  intros.
  rewrite H in H0.
  rewrite H0.
  reflexivity.
Qed.


(** * 用Coq归纳类型定义二叉树 *)

Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.

(** 这个定义说的是，一棵二叉树要么是一棵空树_[Leaf]_，要么有一棵左子树、有一棵右
    子树外加有一个根节点整数标号。我们可以在Coq中写出一些具体的二叉树的例子。*)

Definition tree_example0: tree :=
  Node Leaf 1 Leaf.

Definition tree_example1: tree :=
  Node (Node Leaf 0 Leaf) 2 Leaf.

Definition tree_example2a: tree :=
  Node (Node Leaf 8 Leaf) 100 (Node Leaf 9 Leaf).

Definition tree_example2b: tree :=
  Node (Node Leaf 9 Leaf) 100 (Node Leaf 8 Leaf).

Definition tree_example3a: tree :=
  Node (Node Leaf 3 Leaf) 5 tree_example2a.

Definition tree_example3b: tree :=
  Node tree_example2b 5 (Node Leaf 3 Leaf).


(** Coq中，我们往往可以使用递归函数定义归纳类型元素的性质。Coq中定义递归函数时使
    用的关键字是_[Fixpoint]_。下面两个定义通过递归定义了二叉树的高度和节点个数。*)

Fixpoint tree_height (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => Z.max (tree_height l) (tree_height r) + 1
  end.

Fixpoint tree_size (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => tree_size l + tree_size r + 1
  end.

(** Coq系统“知道”每一棵特定树的高度和节点个数是多少。下面是一些Coq代码的例子。*)

Example Leaf_height:
  tree_height Leaf = 0.
Proof. reflexivity. Qed.

Example tree_example2a_height:
  tree_height tree_example2a = 2.
Proof. reflexivity. Qed.

Example treeexample3b_size:
  tree_size tree_example3b = 5.
Proof. reflexivity. Qed.

(** Coq中也可以定义树到树的函数。下面的_[tree_reverse]_函数把二叉树进行了左右翻转。 *)

Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.

(** 下面是三个二叉树左右翻转的例子：*)

Example Leaf_tree_reverse:
  tree_reverse Leaf = Leaf.
Proof. reflexivity. Qed.

Example tree_example0_tree_reverse:
  tree_reverse tree_example0 = tree_example0.
Proof. reflexivity. Qed.

Example tree_example3_tree_reverse:
  tree_reverse tree_example3a = tree_example3b.
Proof. reflexivity. Qed.

(** 归纳类型有几条基本性质。(1) 归纳定义规定了一种分类方法，以_[tree]_类型为例，
    一棵二叉树_[t]_要么是_[Leaf]_，要么具有形式_[Node l v r]_；(2) 以上的分类之
    间是互斥的，即无论_[l]_、_[v]_与_[r]_取什么值，_[Leaf]_与_[Node l v r]_都不
    会相等；(3) _[Node]_这样的构造子是函数也是单射。这三条性质对应了Coq中的三条
    证明指令：_[destruct]_、_[discriminate]_与_[injection]_。利用它们就可以证明
    几条最简单的性质：*)

Lemma Node_inj_left: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  l1 = l2.
Proof.
  intros.
  injection H as H_l H_v H_r.
  (** 上面的_[injection]_指令使用了_[Node]_是单射这一性质。*)
  rewrite H_l.
  reflexivity.
Qed.

(** 有时，手动为_[injection]_生成的命题进行命名显得很啰嗦，Coq允许用户使用问号占
    位，从而让Coq进行自动命名。*)

Lemma Node_inj_right: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  r1 = r2.
Proof.
  intros.
  injection H as ? ? ?.
  (** 这里，Coq自动命名的结果是使用了_[H]_、_[H0]_与_[H1]_。下面也使用_[apply]_
      指令取代_[rewrite]_简化后续证明。*)
  apply H1.
Qed.

(** 如果不需要用到_[injection]_生成的左右命题，可以将不需要用到的部分用下划线占
    位。*)

Lemma Node_inj_value: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  v1 = v2.
Proof.
  intros.
  injection H as _ ? _.
  apply H.
Qed.

(** 下面引理说：若_[Leaf]_与_[Node l v r]_相等，那么_[1 = 2]_。换言之，_[Leaf]_
    与_[Node l v r]_始终不相等，否则就形成了一个矛盾的前提。*)

Lemma Leaf_Node_conflict: forall l v r,
  Leaf = Node l v r -> 1 = 2.
Proof.
  intros.
  discriminate.
Qed.

(** 下面这个简单性质与_[tree_reverse]_有关。*)

Lemma reverse_result_Leaf: forall t,
  tree_reverse t = Leaf ->
  t = Leaf.
Proof.
  intros.
  (** 下面的_[destruct]_指令根据_[t]_是否为空树进行分类讨论。*)
  destruct t.
  (** 执行这一条指令之后，Coq中待证明的证明目标由一条变成了两条，对应两种情况。
      为了增加Coq证明的可读性，我们推荐大家使用bullet记号把各个子证明过程分割开
      来，就像一个一个抽屉或者一个一个文件夹一样。Coq中可以使用的bullet标记有：
      _[+ - * ++ -- **]_等等*)
  + reflexivity.
    (** 第一种情况是_[t]_是空树的情况。这时，待证明的结论是显然的。*)
  + discriminate H.
    (** 第二种情况下，其实前提_[H]_就可以推出矛盾。可以看出，_[discriminate]_指
        令也会先根据定义化简，再试图推出矛盾。*)
Qed.

(** * 结构归纳法 *)


(** 我们接下去将证明一些关于_[tree_height]_，_[tree_size]_与_[tree_reverse]_的基
    本性质。我们在证明中将会使用的主要方法是归纳法。  

    相信大家都很熟悉自然数集上的数学归纳法。数学归纳法说的是：如果我们要证明某性
    质_[P]_对于任意自然数_[n]_都成立，那么我可以将证明分为如下两步：  
    奠基步骤：证明_[P 0]_成立；  
    归纳步骤：证明对于任意自然数_[n]_，如果_[P n]_成立，那么_[P (n + 1)]_也成
    立。  


    对二叉树的归纳证明与上面的数学归纳法稍有不同。具体而言，如果我们要证明某性质
    _[P]_对于一切二叉树_[t]_都成立，那么我们只需要证明以下两个结论：  

    奠基步骤：证明_[P Leaf]_成立；  
    归纳步骤：证明对于任意二叉树_[l]_ _[r]_以及任意整数标签_[n]_，如果_[P l]_与
    _[P r]_都成立，那么_[P (Node l n r)]_也成立。  

    这样的证明方法就成为结构归纳法。在Coq中，_[induction]_指令表示：使用结构归纳
    法。下面是几个证明的例子。  


    第一个例子是证明_[tree_size]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_size: forall t,
  tree_size (tree_reverse t) = tree_size t.
Proof.
  intros.
  induction t.
  (** 上面这个指令说的是：对_[t]_结构归纳。Coq会自动将原命题规约为两个证明目标，
      即奠基步骤和归纳步骤。*)
  + simpl.
    (** 第一个分支是奠基步骤。这个_[simpl]_指令表示将结论中用到的递归函数根据定
        义化简。*)
    reflexivity.
  + simpl.
    (** 第二个分支是归纳步骤。我们看到证明目标中有两个前提_[IHt1]_以及_[IHt2]_。
        在英文中_[IH]_表示induction hypothesis的缩写，也就是归纳假设。在这个证明
        中_[IHt1]_与_[IHt2]_分别是左子树_[t1]_与右子树_[t2]_的归纳假设。 *)

    rewrite IHt1.
    rewrite IHt2.
    lia.
Qed.


(** 第二个例子很类似，是证明_[tree_height]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_height: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHt1.
    rewrite IHt2.
    lia.
    (** 注意：_[lia]_指令也是能够处理_[Z.max]_与_[Z.min]_的。*)
Qed.

(** 下面我们将通过重写上面这一段证明，介绍Coq证明语言的一些其他功能。*)

Lemma reverse_height_attempt2: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t; simpl.
  (** 在Coq证明语言中可以用分号将小的证明指令连接起来形成大的证明指令，其中
      _[tac1 ; tac2]_这个证明指令表示先执行指令_[tac1]_，再对于_[tac1]_生成的每
      一个证明目标执行_[tac2]_。分号是右结合的。*)
  + reflexivity.
  + simpl.
    lia.
Qed.

(************)
(** 习题：  *)
(************)

Lemma reverse_involutive: forall t,
  tree_reverse (tree_reverse t) = t.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 加强归纳 *)


(** 下面证明_[tree_reverse]_是一个单射。*)

Lemma tree_reverse_inj: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  (** 这个引理的Coq证明需要我们特别关注：真正需要归纳证明的结论是什么？如果选择
      对_[t1]_做结构归纳，那么究竟是归纳证明对于任意_[t2]_上述性质成立，还是归纳
      证明对于某“特定”的_[t2]_上述性质成立？如果我们按照之前的Coq证明习惯，用
      _[intros]_与_[induction t1]_两条指令开始证明，那就表示用归纳法证明一条关于
      “特定”_[t2]_的性质。*)
  intros.
  induction t1.
  + destruct t2.
    (** 奠基步骤的证明可以通过对_[t2]_的分类讨论完成。*)
    - reflexivity.
      (** 如果_[t2]_是空树，那么结论是显然的。*)
    - simpl in H.
      discriminate H.
      (** 如果_[t2]_是非空树，那么前提_[H]_就能导出矛盾。如上面指令展示的那样，
          _[simpl]_指令也可以对前提中的递归定义化简。当然，在这个证明中，由于之
          后的_[discriminate]_指令也会完成自动化简，这条_[simpl]_指令其实是可以
          省略的。*)
  +
Abort.

(** 进入归纳步骤的证明时，不难发现，证明已经无法继续进行。因为需要使用的归纳假设
    并非关于原_[t2]_值的性质。正确的证明方法是用归纳法证明一条对于一切_[t2]_的结
    论。*)

Lemma tree_reverse_inj: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  intros t1.
  (** 上面这条_[intros 1t]_指令可以精确地将_[t1]_放到证明目标的前提中，同时却将
      _[t2]_保留在待证明目标的结论中。*)
  induction t1; simpl; intros.
  + destruct t2.
    - reflexivity.
    - discriminate H.
  + destruct t2.
    - discriminate H.
    - injection H as ? ? ?.
      rewrite (IHt1_1 _ H1).
      rewrite (IHt1_2 _ H).
      rewrite H0.
      reflexivity.
Qed.

(** 当然，上面这条引理其实可以不用归纳法证明。下面的证明中使用了前面证明的结论：
    _[reverse_involutive]_。*)

Lemma tree_reverse_inj_again: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  intros.
  rewrite <- (reverse_involutive t1), <- (reverse_involutive t2).
  rewrite H.
  reflexivity.
Qed.




