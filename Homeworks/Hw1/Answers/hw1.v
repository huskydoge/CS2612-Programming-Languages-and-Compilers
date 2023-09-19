(** 下面这行指令表示导入课件Intro.v中的定义与证明。在导入之前，你需要完成下面几
    个步骤：
    (1) 将 CoqIntro.v 与本文件放在一个目录中
    (2) 在同一个目录下创建 _CoqProject 文件（无后缀名）
    (3) 在 _CoqProject 中写入一行 -Q . PL
    (4) 关闭并重新打开CoqIDE，打开 CoqIntro.v，点击 Make、 Compile Buffer
    (5) 检查是否成功生成了 CoqIntro.vo 文件
    (6) 重新在CoqIDE打开本文件，此时下面加载指令即可成功执行。*)

Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.CoqIntro.
Local Open Scope Z.

(** 请完成课后阅读后作答。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
  unfold shift_up1, func_plus.
  intros.
  reflexivity.
Qed.
 (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
  unfold mono.
  intros.
  lia.
Qed.

(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(************)
(** 习题：  *)
(************)

(** 请证明函数加法能保持单调性。*)

Lemma mono_func_plus: forall f g,
  mono f ->
  mono g ->
  mono (func_plus f g).
Proof.
  unfold mono, func_plus.
  intros f g Hf Hg n m.
  pose proof Hf n m.
  pose proof Hg n m.
  lia.
Qed.


(* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


