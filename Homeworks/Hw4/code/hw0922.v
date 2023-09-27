Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.CoqIntro.
Require Import PL.InductiveType.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面关于结合律的性质。*)

Definition power2 (f: Z -> Z -> Z) (x: Z): Z :=
  f x x.

Definition power4 (f: Z -> Z -> Z) (x: Z): Z :=
  f x (f x (f x x)).

Fact power2_power2: forall f a,
  assoc f ->
  power2 f (power2 f a) = power4 f a.
Proof.
  unfold assoc, power2, power4.
  intros.
  rewrite <- H.
  reflexivity.
Qed.

 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)



(************)
(** 习题：  *)
(************)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  induction t.
  + simpl.
    reflexivity.
  + simpl.
    lia.
Qed.
  

(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)


Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros t.
  induction t.
  + discriminate.
  + intros.
    injection H as H1 H2 H3.
    rewrite H2.
    rewrite <- H3.
    rewrite <- H1.
    rewrite (reverse_involutive t1), (reverse_involutive t2).
    reflexivity.
Qed.
    
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Proof.
  intros t.
  induction t.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHt2.
    reflexivity.
Qed.    
  
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)




