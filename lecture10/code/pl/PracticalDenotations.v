Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 表示64位整数运算的整数表达式语义 *)

Module DntSem_SimpleWhile6.
Import Lang_SimpleWhile.


(** 程序状态的修改：  

    Coq定义：*)

Definition state: Type := var_name -> int64.

(** 这里_[int64]_是CompCert库中定义的64位整数，该定义是_[compcert.lib.Integers]_
    这一头文件导入的。除了_[int64]_的类型定义，CompCert还定义了64位整数的运算并
    证明相关运算的一些基本性质，例如_[Int64.add]_表示64位算术加法，_[Int64.and]_
    表示按位做『与』运算。  



    除了上述表达算术运算、位运算的函数外，还有3个64位整数相关的函数十分常用，分
    别是：_[Int64.repr]_, _[Int64.signed]_, _[Int64.unsigned]_。另外，下面几个常
    数定义了有符号64位整数与无符号64位整数的大小边界：_[Int64.max_unsigned]_,
    _[Int64.max_signed]_, _[Int64.min_signed]_。  

    除了修改程序状态的定义，还需要相应修改程序证整数类型表达式的语义。在Coq中，
    _[eval_expr_int e]_的类型就需要改为_[state -> int64]_。*)

Definition add_sem (D1 D2: state -> int64) s: int64 :=
  Int64.add (D1 s) (D2 s).

Definition sub_sem (D1 D2: state -> int64) s: int64 :=
  Int64.sub (D1 s) (D2 s).

Definition mul_sem (D1 D2: state -> int64) s: int64 :=
  Int64.mul (D1 s) (D2 s).

Definition const_sem (n: Z) (s: state): int64 :=
  Int64.repr n.

Definition var_sem (X: var_name) (s: state): int64 :=
  s X.

Fixpoint eval_expr_int (e: expr_int) : state -> int64 :=
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


End DntSem_SimpleWhile6.

(** * 将运算越界定义为表达式求值错误 - 用部分函数 *)

Module DntSem_SimpleWhile7.
Import Lang_SimpleWhile.

Definition state: Type := var_name -> int64.

Ltac int64_lia :=
  change Int64.min_signed with (-9223372036854775808) in *;
  change Int64.max_signed with 9223372036854775807 in *;
  lia.


(** 在讲解并实现简单解释器之前，我们曾经约定while语言的算术运算语义基本遵循C标准
    的规定。特别的，有符号64位整数的运算越界应当被视为程序错误（C11标准6.5章节第
    5段落）。然而，这一点并未在上面定义中得到体现。  

    为了解决这一问题，我们需要能够在定义中表达『程序表达式求值出错』这一概念。这
    在数学上有两种常见方案。其一是将求值结果由64位整数集合改为64位整数或求值失
    败。  



    在Coq中可以使用_[option]_类型描述相关概念。*)


Print option.

(** 具体而言，对于任意Coq类型_[A]_，_[option A]_的元素要么是_[Some a]_（其中
    _[a]_是_[A]_的元素）要么是_[None]_。可以看到_[option]_也是一个Coq归纳类型，
    只不过其定义中并不需要对自身归纳。我们可以像处理先前其他归纳类型一样使用Coq
    中的_[match]_定义相关的函数或性质，例如：*)

Definition option_plus1 (o: option Z): option Z :=
  match o with
  | Some x => Some (x + 1)
  | None => None
  end.

(** 例如上面这一定义说的是：如果_[o]_的值是_[None]_那么就返回_[None]_，如果_[o]_
    的值是某个整数（_[Some]_的情况），那就将它加一返回。  

    利用类似_[option]_类型可以改写表达式的语义定义。*)

Definition const_sem (n: Z) (s: state): option int64 :=
  if (n <=? Int64.max_signed) && (n >=? Int64.min_signed)
  then Some (Int64.repr n)
  else None.

Definition var_sem (x: var_name) (s: state): option int64 :=
  Some (s x).

Definition add_sem (D1 D2: state -> option int64) (s: state): option int64 :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Int64.signed i1 + Int64.signed i2 <=? Int64.max_signed) &&
         (Int64.signed i1 + Int64.signed i2 >=? Int64.min_signed)
      then Some (Int64.add i1 i2)
      else None
  | _, _ => None
  end.

Definition sub_sem (D1 D2: state -> option int64) (s: state): option int64 :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Int64.signed i1 - Int64.signed i2 <=? Int64.max_signed) &&
         (Int64.signed i1 - Int64.signed i2 >=? Int64.min_signed)
      then Some (Int64.sub i1 i2)
      else None
  | _, _ => None
  end.

Definition mul_sem (D1 D2: state -> option int64) (s: state): option int64 :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Int64.signed i1 * Int64.signed i2 <=? Int64.max_signed) &&
         (Int64.signed i1 * Int64.signed i2 >=? Int64.min_signed)
      then Some (Int64.mul i1 i2)
      else None
  | _, _ => None
  end.

(** 最终，整数类型表达式的语义可以归结为下面递归定义。*)

Fixpoint eval_expr_int (e: expr_int): state -> option int64 :=
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

(** 上述定义中除了用到Coq的_[option]_类型，还用到了Coq的_[bool]_类型。*)

Print bool.

(** 根据定义_[bool]_类型只有两种可能的取值：_[true]_与_[false]_。请注意，Coq中的
    _[bool]_类型与命题（_[Prop]_类型）并不相同，前者专门用于关于真与假的真值运
    算，而后者则可以描述关于任意、存在等真假难以判定、无法计算真值的命题。上面的
    _[eval_expr_int]_定义要用于计算出_[option int64]_类型的结果，因此就只能使用
    _[bool]_类型的Coq函数来做判定了，他们分别是_[<=?]_, _[>=?]_与_[&&]_。*)

Check 1 <=? 2.
Check 1 <= 2.

(** 可以看到，_[1 <=? 2]_是用_[bool]_类型表达的判断两数大小的结果，这一符号对应
    的定义是：_[Z.leb 1 2]_。而_[1 <= 2]_则是关于两数大小关系的命题，这一符号对
    应的定义是：_[Z.le 1 2]_。Coq标准库中也证明了两者的联系。*)

Check Z.leb_le.

(** 这个定理说的是：_[forall n m : Z, (n <=? m) = true <-> n <= m]_。当然，Coq标
    准库中还有很多类似的有用的性质，这里就不再一一罗列了，相关信息也可以通过
    _[Search Z.leb]_或_[Search Z.le]_等方法查找。  

    最后，在Coq中，可以用_[&&]_表示布尔值的合取（Coq定义是_[andb]_）并且使用
    _[if]_，_[then]_，_[else]_针对布尔表达式求值为真以及为假的情况分别采取不同的
    求值方法。将这些定义组合在一起，就得到了上面的_[eval_expr_int]_定义。  

    下面是一些证明自动化指令（可以跳过）。*)

Ltac int64_arith_simpl :=
  repeat
  match goal with
  | |- context [if ?X then Some ?A else None] =>
         match X with
         | context [?A <=? ?B] =>
            first
            [ assert (A <= B) as HHH by int64_lia;
              apply Z.leb_le in HHH;
              rewrite HHH; clear HHH]
         | context [?A >=? ?B] =>
            first
            [ assert (B <= A) as HHH by int64_lia;
              apply Z.geb_le in HHH;
              rewrite HHH; clear HHH]
         | context [true && ?b] => change (true && b) with b
         | context [false && ?b] => change (false && b) with false
         end
  | |- context [if true then ?A else ?B] =>
         change (if true then A else B) with A
  | |- context [if false then ?A else ?B] =>
         change (if false then A else B) with B
  | |- context [match Some ?A with | Some _ => _ | None => _ end] =>
         cbv beta iota
  | |- context [Int64.signed (Int64.repr ?n)] =>
         rewrite (Int64.signed_repr n) by int64_lia
  end.

(** 我们可以在Coq中证明一些关于表达式指称语义的基本性质。*)

Example eval_expr_int_fact0: forall st,
  st "x" = Int64.repr 0 ->
  eval_expr_int [["x" + 1]] st = Some (Int64.repr 1).
Proof.
  intros.
  simpl.
  unfold add_sem, var_sem, const_sem.
  rewrite H.
  int64_arith_simpl.
  reflexivity.
Qed.


End DntSem_SimpleWhile7.

Module DntSem_SimpleWhile8.
Import Lang_SimpleWhile
       DntSem_SimpleWhile7.


(** 上面定义中有三个分支的定义是相似，我们也可以统一定义。  

    这里，_[Zfun: Z -> Z -> Z]_可以看做对整数加法（_[Z.add]_)、整数减法
    （_[Z.sub]_）与整数乘法（_[Z.mul]_）的抽象。而
     _[i64fun: int64 -> int64 -> int64]_可以看做对64位整数二元运算的抽象。*)

Definition arith_sem
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> option int64)
             (s: state): option int64 :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Zfun (Int64.signed i1) (Int64.signed i2)
                               <=? Int64.max_signed) &&
         (Zfun (Int64.signed i1) (Int64.signed i2)
                               >=? Int64.min_signed)
      then Some (int64fun i1 i2)
      else None
  | _, _ => None
  end.

(** 例如，下面将_[Zfun]_取_[Z.add]_、_[int64fun]_取_[Int64.add]_代入：*)

Example arith_sem_add_fact: forall D1 D2 s,
  arith_sem Z.add Int64.add D1 D2 s =
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Int64.signed i1 + Int64.signed i2
                               <=? Int64.max_signed) &&
         (Int64.signed i1 + Int64.signed i2
                               >=? Int64.min_signed)
      then Some (Int64.add i1 i2)
      else None
  | _, _ => None
  end.
Proof. intros. reflexivity. Qed.

(** 这样，_[eval_expr_int]_的定义就可以简化为：*)

Fixpoint eval_expr_int (e: expr_int):
  state -> option int64 :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem Z.add Int64.add
        (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem Z.sub Int64.sub
        (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem Z.mul Int64.mul
        (eval_expr_int e1) (eval_expr_int e2)
  end.


End DntSem_SimpleWhile8.

(** * 将运算越界定义为表达式求值错误 - 用二元关系 *)

(** 上面我们讨论了将表达式语义定义为程序状态到_[option int64]_的函数这一方案。下
    面我们探讨另一种描述程序运行出错或未定义行为的方案，即将表达式的语义定义为程
    序状态与_[int64]_之间的二元关系。  


    下面给出相应的Coq定义。首先定义64位整数之间在有符号64位整数范围内的运算关系。*)

Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    i = Int64.repr res /\
    Int64.min_signed <= res <= Int64.max_signed.

Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    res < Int64.min_signed \/ res > Int64.max_signed.

Module DntSem_SimpleWhile9.
Import Lang_SimpleWhile.

(** 接下去利用表达式与64位整数值间的二元关系表达『程序表达式求值出错』这一概念。
    具体而言，如果表达式_[e]_在程序状态_[s]_上能成果求值且求值结果为_[i]_，那么
    _[s]_与_[i]_这个有序对就在_[e]_的语义中。*)

Definition state: Type := var_name -> int64.


(** 下面定义统一刻画了三种算术运算的语义。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

(** 一个表达式的语义分为两部分：求值成功的情况与求值出错的情况。*)

Record denote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

(** 下面_[Notation]_定义用于提供便捷易懂的表示方法，可以忽略其中的声明细节。*)

Notation "x '.(nrm)'" := (nrm x) (at level 1).
Notation "x '.(err)'" := (err x) (at level 1).


(** Coq中的_[Record]_与许多程序语言中的结构体是类似的。在上面定义中，每个表达式
    的语义_[D: denote]_都有两个域：_[D.(nrm)]_与_[D.(err)]_分别描述前面提到的两
    种情况。*)

Definition arith_sem1 Zfun (D1 D2: denote): denote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition const_sem (n: Z): denote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition var_sem (X: var_name): denote :=
  {|
    nrm := fun s i => i = s X;
    err := ∅;
  |}.

(** 最终，整数类型表达式的语义可以归结为下面递归定义。*)

Fixpoint eval_expr_int (e: expr_int): denote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem1 Z.add (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem1 Z.sub (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem1 Z.mul (eval_expr_int e1) (eval_expr_int e2)
  end.



End DntSem_SimpleWhile9.

(** * 未初始化的变量 *)

(** 在C语言和很多实际编程语言中，都不允许或不建议在运算中或赋值中使用未初始化的
    变量的值。若要根据这一设定定义程序语义，那么就需要修改程序状态的定义。变量的
    值可能是一个64位整数，也可能是未初始化。*)

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

Module DntSem_SimpleWhile10.
Import Lang_SimpleWhile.

(** 程序状态就变成变量名到_[val]_的函数。*)

Definition state: Type := var_name -> val.

(** 表达式的指称依旧包含原有的两部分。*)

Record denote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

Notation "x '.(nrm)'" := (nrm x) (at level 1).
Notation "x '.(err)'" := (err x) (at level 1).

(** 下面这些Coq定义也不变。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: denote): denote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition const_sem (n: Z): denote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

(** 唯有整数类型表达式中变量的语义需要重新定义。*)

Definition var_sem (X: var_name): denote :=
  {|
    nrm := fun s i => s X = Vint i;
    err := fun s => s X = Vuninit;
  |}.

(** 最终，整数类型表达式的语义还是可以写成同样的递归定义。*)

Fixpoint eval_expr_int (e: expr_int): denote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem1 Z.add (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem1 Z.sub (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem1 Z.mul (eval_expr_int e1) (eval_expr_int e2)
  end.

End DntSem_SimpleWhile10.

(** * While语言的语义 *)

(** 有了上面这些准备工作，我们可以定义完整While语言的语义。完整While语言中支持更
    多运算符，要描述除法和取余运算符的行为，要定义不同于加减乘的运算关系。下面定
    义参考了C标准对于有符号整数除法和取余的规定。*)

Definition arith_compute2_nrm
             (int64fun: int64 -> int64 -> int64)
             (i1 i2 i: int64): Prop :=
  i = int64fun i1 i2 /\
  Int64.signed i2 <> 0 /\
  (Int64.signed i1 <> Int64.min_signed \/
   Int64.signed i2 <> - 1).

Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
   Int64.signed i2 = - 1).

(** 下面定义的比较运算关系利用了CompCert库定义的_[comparison]_类型和_[Int64.cmp]_
    函数。*)

Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: int64): Prop :=
  i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.

(** 一元运算的行为比较容易定义：*)

Definition neg_compute_nrm (i1 i: int64): Prop :=
  i = Int64.neg i1 /\
  Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
  Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
  i1 = Int64.repr 0 /\ i = Int64.repr 1.

(** 最后，二元布尔运算的行为需要考虑短路求值的情况。下面定义中的缩写_[SC]_表示
    short circuit。*)

Definition SC_and_compute_nrm (i1 i: int64): Prop :=
  i1 = Int64.repr 0 /\ i = Int64.repr 0.

Definition SC_or_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 1.

Definition NonSC_and (i1: int64): Prop :=
  Int64.signed i1 <> 0.

Definition NonSC_or (i1: int64): Prop :=
  i1 = Int64.repr 0.

Definition NonSC_compute_nrm (i2 i: int64): Prop :=
  i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
  Int64.signed i2 <> 0 /\ i = Int64.repr 1.


Module DntSem_While1.
Import Lang_While
       BWFix Sets_CPO.

(** 程序状态依旧是变量名到64位整数或未初始化值的函数，表达式的指称依旧包含成功求
    值情况与求值失败情况这两部分。*)

Definition state: Type := var_name -> val.

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

(** 以下为语义定义。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

(** 所有运算符的语义中，二元布尔运算由于涉及短路求值，其定义是最复杂的。*)

Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

(** 最终我们可以将所有一元运算与二元运算的语义汇总起来：*)

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

(** 最后补上常数和变量的语义即可得到完整的表达式语义。*)

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition var_sem (X: var_name): EDenote :=
  {|
    nrm := fun s i => s X = Vint i;
    err := fun s => s X = Vuninit;
  |}.

Fixpoint eval_expr (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  end.

(** 基于表达式的指称语义，可以证明一些简单性质。*)

Lemma const_plus_const_nrm:
  forall (n m: Z) (s: state) (i: int64),
    (eval_expr (EBinop OPlus (EConst n) (EConst m))).(nrm) s i ->
    (eval_expr (EConst (n + m))).(nrm) s i.
Proof.
  intros.
  simpl in H; unfold arith_sem1_nrm, arith_compute1_nrm in H.
  simpl.
  destruct H as [i1 [i2 [? [? [? ?] ] ] ] ].
  destruct H, H0.
  rewrite H1.
  apply Int64.signed_repr in H3.
  apply Int64.signed_repr in H4.
  rewrite <- H in H3.
  rewrite <- H0 in H4.
  rewrite <- H3, <- H4.
  tauto.
Qed.

(** 下面定义程序语句的语义。程序语句的语义包含三种情况：正常运行终止、运行出错以
    及安全运行但不终止。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

(** 空语句的语义：*)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

(** 赋值语句的语义：*)

Definition asgn_sem
             (X: var_name)
             (D: EDenote): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        D.(nrm) s1 i /\ s2 X = Vint i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    err := D.(err);
    inf := ∅;
  |}.

(** 顺序执行语句的语义：*)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

(** 条件分支语句的语义：*)

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.




(** While循环语句不终止的情况分为两种：每次执行循环体程序都正常运行终止但是
    由于一直满足循环条件将执行无穷多次循环体；某次执行循环体时，执行循环体的过程
    本身不终止。  


    下面定义的_[is_inf]_描述了以下关于程序状态集合_[X]_的性质：从集
    合_[X]_中的任意一个状态出发，计算循环条件的结果都为真（也不会计算出错），进
    入循环体执行后，要么正常运行终止并且终止于另一个（可以是同一个）_[X]_集合中
    的状态上，要么循环体运行不终止。*)

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

(** 这样一来，循环不终止的情况可以定义为所有满足_[is_inf]_性质的集合的并集。*)

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := BW_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_false D0);
    err := BW_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_true D0 ∘ D1.(err) ∪ D0.(err));
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(** 程序语句的语义可以最后表示成下面递归函数。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.




End DntSem_While1.

(** * Knaster-Tarski不动点定理 *)


Module KTFix.
Import BWFix.

(** 下面是这一不动点定理的Coq证明。*)

Local Open Scope order_scope.

(** 首先定义完备格。*)

Definition is_lub {A: Type} {RA: Order A} (X: A -> Prop) (a: A): Prop :=
  is_ub X a /\ is_lb (is_ub X) a.

Definition is_glb {A: Type} {RA: Order A} (X: A -> Prop) (a: A): Prop :=
  is_lb X a /\ is_ub (is_lb X) a.

Class Lub (A: Type): Type :=
  lub: (A -> Prop) -> A.

Class Glb (A: Type): Type :=
  glb: (A -> Prop) -> A.

Class LubProperty (A: Type) {RA: Order A} {LubA: Lub A}: Prop :=
  lub_is_lub: forall X: A -> Prop, is_lub X (lub X).

Class GlbProperty (A: Type) {RA: Order A} {GlbA: Glb A}: Prop :=
  glb_is_glb: forall X: A -> Prop, is_glb X (glb X).

Lemma lub_sound: forall {A: Type} `{LubPA: LubProperty A},
  forall X: A -> Prop, is_ub X (lub X).
Proof. intros. destruct (lub_is_lub X). tauto. Qed.

Lemma lub_tight: forall {A: Type} `{LubPA: LubProperty A},
  forall X: A -> Prop, is_lb (is_ub X) (lub X).
Proof. intros. destruct (lub_is_lub X). tauto. Qed.

Lemma glb_sound: forall {A: Type} `{GlbPA: GlbProperty A},
  forall X: A -> Prop, is_lb X (glb X).
Proof. intros. destruct (glb_is_glb X). tauto. Qed.

Lemma glb_tight: forall {A: Type} `{GlbPA: GlbProperty A},
  forall X: A -> Prop, is_ub (is_lb X) (glb X).
Proof. intros. destruct (glb_is_glb X). tauto. Qed.

Class CompleteLattice_Setoid (A: Type)
        {RA: Order A} {EA: Equiv A} {LubA: Lub A} {glbA: Glb A}: Prop :=
{
  CL_PartialOrder:> PartialOrder_Setoid A;
  CL_LubP:> LubProperty A;
  CL_GlbP:> GlbProperty A
}.

(** 下面基于完备格与单调函数的定义证明Knaster-Tarski不动点定理。*)

Definition KT_LFix
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}
             (f: A -> A): A :=
  glb (fun a => f a <= a).

Lemma KT_LFix_is_pre_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    f (KT_LFix f) <= KT_LFix f.
Proof.
  intros.
  unfold KT_LFix.
  apply glb_tight; unfold is_lb; intros.
  rewrite <- H0.
  apply H.
  apply glb_sound.
  apply H0.
Qed.

Lemma KT_LFix_is_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    f (KT_LFix f) == KT_LFix f.
Proof.
  intros.
  pose proof KT_LFix_is_pre_fix f H.
  apply antisymmetricity_setoid.
  + apply H0.
  + apply glb_sound.
    apply H, H0.
Qed.

Lemma KT_LFix_is_least_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    f a == a ->
    KT_LFix f <= a.
Proof.
  intros.
  apply glb_sound.
  apply reflexivity_setoid.
  apply H0.
Qed.

(** 在完备格中大与小这两个方向是对称的，所以我们也可以定义Knaster-Tarski最大
    不动点，并证明相关性质。*)

(************)
(** 习题：  *)
(************)


Definition KT_GFix
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}
             (f: A -> A): A :=
  lub (fun a => a <= f a).

Lemma KT_GFix_is_post_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    KT_GFix f <= f (KT_GFix f).
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  unfold KT_GFix.
  apply lub_tight; unfold is_ub; intros.
  transitivity (f a'); [apply H0 |].
  apply H.
  apply lub_sound.
  apply H0.
Qed.

Lemma KT_GFix_is_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    f (KT_GFix f) == KT_GFix f.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  pose proof KT_GFix_is_post_fix f H.
  apply antisymmetricity_setoid.
  + apply lub_sound.
    apply H, H0.
  + apply H0.
Qed.

Lemma KT_GFix_is_greatest_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    f a == a ->
    a <= KT_GFix f.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  apply lub_sound.
  apply reflexivity_setoid.
  symmetry.
  apply H0.
Qed.

Local Close Scope order_scope.

End KTFix.

(** 事实上，我们可以在Coq中证明所有的幂集上的包含关系都是完备格。以下证明代码可以跳过。*)

Module Sets_CL.
Import BWFix KTFix Sets_CPO.


Local Open Scope sets_scope.
Local Open Scope order_scope.

Instance Lub_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Lub T :=
  Sets.general_union.

Instance Glb_sets
           {T: Type}
           {_SETS: Sets.SETS T}: Glb T :=
  Sets.general_intersect.

Instance LubP_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: LubProperty T.
Proof.
  split.
  + unfold lub, Lub_sets, is_ub.
    intros.
    apply Sets_included_general_union.
    tauto.
  + unfold lub, Lub_sets, is_lb, is_ub.
    intros.
    apply Sets_general_union_included.
    intros.
    apply H.
    tauto.
Qed.

Instance GlbP_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: GlbProperty T.
Proof.
  split.
  + unfold glb, Glb_sets, is_lb.
    intros.
    apply Sets_general_intersect_included.
    tauto.
  + unfold glb, Glb_sets, is_lb, is_ub.
    intros.
    apply Sets_included_general_intersect.
    intros.
    apply H.
    tauto.
Qed.

Instance CL_sets
           {T: Type}
           {_SETS: Sets.SETS T}
           {_SETS_Properties: SETS_Properties T}: CompleteLattice_Setoid T.
Proof.
  split.
  + apply PO_sets.
  + apply LubP_sets.
  + apply GlbP_sets.
Qed.

Local Close Scope sets_scope.
Local Close Scope order_scope.

End Sets_CL.


(** * 用Knaster-Tarski不动点改写While语言的语义 *)

Module DntSem_While2.
Import Lang_While
       DntSem_While1 EDenote CDenote
       BWFix KTFix Sets_CPO Sets_CL.


Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := BW_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_false D0);
    err := BW_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_true D0 ∘ D1.(err) ∪ D0.(err));
    inf := KT_GFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_true D0 ∘ D1.(inf));
  |}.

(** 程序语句的语义可以最后表示成下面递归函数。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.


End DntSem_While2.

(** * WhileDeref语言的语义 *)

Module DntSem_WhileDeref.
Import Lang_While.
Import Lang_WhileDeref.

(** 程序状态：*)

Record state: Type := {
  vars: var_name -> val;
  mem: int64 -> option val;
}.

Notation "s '.(vars)'" := (vars s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

(** 这里，_[s.(vars)]_表示程序状态_[s]_上变量的值，_[s.(mem)]_表示程序状态_[s]_
    上的内存信息，地址用64位有符号整数表示，一个地址上的值是_[Some]_表示有读写权
    限，_[None]_表示没有读写权限。  

    下面定义表达式的指称语义。表达式指称的定义、二元运算、一元运算与常量的语义都
    与原先相同。*)

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

(** 程序表达式为单个变量时的语义需要做少许修改，其语义定义应当使用程序状态中变量
    的部分：_[s.(vars)]_。*)

Definition var_sem (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(vars) X = Vint i;
    err := fun s => s.(vars) X = Vuninit;
  |}.

(** 最后，需要新定义『解引用』的语义，其语义定义应当使用程序状态中内存的部分：
    _[s.(mem)]_。*)

Definition deref_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Some (Vint i).

Definition deref_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

(** 在递归定义的表达式语义中，也需要加上『解引用』的情形。*)

Fixpoint eval_expr (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  | EDeref e1 =>
      deref_sem (eval_expr e1)
  end.

(** 在表达式语义定义的基础上，_[test_true]_与_[test_false]_的定义不变。*)

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(** 程序语句的指称定义不变，依然包括三种情况：正常运行终止、运行出错以及运行不终
    止。空语句、顺序执行、条件分支语句与while循环语句的语义定义也不变。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (iter_nrm_lt_n D0 D1);
    err := ⋃ (iter_err_lt_n D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(** 需要新定义的是两种赋值语句的语义。变量赋值语句的语义与原赋值语句的语义基本相
    同，但需要额外说明对变量赋值不修改内存上的值。*)

Definition asgn_var_sem
             (X: var_name)
             (D: EDenote): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        D.(nrm) s1 i /\ s2.(vars) X = Vint i /\
        (forall Y, X <> Y -> s2.(vars) Y = s1.(vars) Y) /\
        (forall p, s1.(mem) p = s2.(mem) p);
    err := D.(err);
    inf := ∅;
  |}.

(** 向某地址赋值的语义是根据表达式修改内存上的值而不改变任意一个程序变量的值。*)

Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(vars) X = s2.(vars) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = None.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

(** 在递归定义的程序语句语义中，要加上这两种赋值语句的语义。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_expr e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_expr e1) (eval_expr e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.


End DntSem_WhileDeref.

(** * WhileD语言的语义 *)

Module DntSem_WhileD.
Import Lang_While.
Import Lang_WhileD.

(** 程序状态：*)

Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

(** 由于表达式中存在取地址操作，我们无法继续沿用原先定义的表达式指称。*)

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

(** 『解引用』表达式既可以用作右值也可以用作左值。其作为右值是的语义就是原先我们
    定义的『解引用』语义。*)

Definition deref_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Some (Vint i).

Definition deref_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

(** 当程序表达式为单个变量时，它也可以同时用作左值或右值。下面先定义其作为左值时
    的存储地址。*)

Definition var_sem_l (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(env) X = i;
    err := ∅;
  |}.

(** 基于此，可以又定义它作为右值时的值。*)

Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).

(** 最后，我们可以用互递归函数（mutually recursive function）在Coq中定义表达式的
    语义。需注意，解引用表达式_[* e]_作为左值时的存储地址就是_[e]_作为右值时的
    值，而取地址表达式_[& e]_作为右值时的值就是_[e]_作为左值时的存储地址。这都不
    需要在额外定义。同时，常量、一元运算、二元运算、取地址表达式这些都不能用作左
    值表达式。*)

Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r e1) (eval_r e2)
  | EUnop op e1 =>
      unop_sem op (eval_r e1)
  | EDeref e1 =>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 =>
      eval_l e1
  end
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

(** 这里_[test_true]_与_[test_false]_的定义不变，不过之后只会将其作用在表达式的
    右值上。*)

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(** 程序语句的指称定义不变，依然包括三种情况：正常运行终止、运行出错以及运行不终
    止。空语句、顺序执行、条件分支语句与while循环语句的语义定义也不变。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (iter_nrm_lt_n D0 D1);
    err := ⋃ (iter_err_lt_n D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(** 向地址赋值的语义与原先定义基本相同，只是现在需要规定所有变量的地址不被改变，
    而非所有变量的值不被改变。*)

Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = None.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

(** 变量赋值的行为可以基于此定义。*)

Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

(** 在递归定义的程序语句语义中，只会直接使用表达式用作右值时的值。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r e1) (eval_r e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  end.


End DntSem_WhileD.

(** * WhileDC语言的语义 *)

Module DntSem_WhileDC.
Import Lang_While.
Import Lang_WhileDC.

(** 程序状态与表达式语义的定义不变。*)

Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition deref_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Some (Vint i).

Definition deref_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

Definition var_sem_l (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(env) X = i;
    err := ∅;
  |}.

Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).

Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r e1) (eval_r e2)
  | EUnop op e1 =>
      unop_sem op (eval_r e1)
  | EDeref e1 =>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 =>
      eval_l e1
  end
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(** 由于在程序语句中加入了控制流，程序语句的指称定义需要做相应改变。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  brk: state -> state -> Prop;
  cnt: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(brk)'" := (CDenote.brk x)
  (at level 1).

Notation "x '.(cnt)'" := (CDenote.cnt x)
  (at level 1).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.


(** 空语句的语义 *)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    brk := ∅;
    cnt := ∅;
    err := ∅;
    inf := ∅;
  |}.

(** Break语句的语义 *)

Definition brk_sem: CDenote :=
  {|
    nrm := ∅;
    brk := Rels.id;
    cnt := ∅;
    err := ∅;
    inf := ∅;
  |}.

(** Continue语句的语义 *)

Definition cnt_sem: CDenote :=
  {|
    nrm := ∅;
    brk := ∅;
    cnt := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

(** 顺序执行语句的语义 *)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    brk := D1.(brk) ∪ (D1.(nrm) ∘ D2.(brk));
    cnt := D1.(cnt) ∪ (D1.(nrm) ∘ D2.(cnt));
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

(** If语句的语义 *)

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    brk := (test_true D0 ∘ D1.(brk)) ∪
           (test_false D0 ∘ D2.(brk));
    cnt := (test_true D0 ∘ D1.(cnt)) ∪
           (test_false D0 ∘ D2.(cnt));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = None.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    brk := ∅;
    cnt := ∅;
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

Module WhileSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          (D1.(cnt) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          D1.(brk))) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ iter_err_lt_n D0 D1 n0) ∪
         (D1.(cnt) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D1.(nrm) ∘ X) ∪
         (D1.(cnt) ∘ X) ∪
         D1.(inf)).

End WhileSem.

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (WhileSem.iter_nrm_lt_n D0 D1);
    brk := ∅;
    cnt := ∅;
    err := ⋃ (WhileSem.iter_err_lt_n D0 D1);
    inf := Sets.general_union (WhileSem.is_inf D0 D1);
  |}.

Definition do_while_sem
             (D0: CDenote)
             (D1: EDenote): CDenote :=
  {|
    nrm := (D0.(nrm) ∪ D0.(cnt)) ∘
           ⋃ (WhileSem.iter_nrm_lt_n D1 D0);
    brk := ∅;
    cnt := ∅;
    err := D0.(err) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            ⋃ (WhileSem.iter_err_lt_n D1 D0));
    inf := D0.(inf) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            Sets.general_union (WhileSem.is_inf D1 D0));
  |}.

Module ForSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D2.(nrm) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          (D2.(cnt) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          D2.(brk))) ∪
      (test_false D0)
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         D2.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ X) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ X) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         D2.(inf)).

End ForSem.

Definition for_sem
             (D: CDenote)
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote): CDenote :=
  {|
    nrm := D.(nrm) ∘ ⋃ (ForSem.iter_nrm_lt_n D0 D1 D2);
    brk := ∅;
    cnt := ∅;
    err := D.(err) ∪ (D.(nrm) ∘ ⋃ (ForSem.iter_err_lt_n D0 D1 D2));
    inf := D.(inf) ∪ (D.(nrm) ∘ Sets.general_union (ForSem.is_inf D0 D1 D2));
  |}.

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r e1) (eval_r e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  | CDoWhile c1 e =>
      do_while_sem (eval_com c1) (eval_r e)
  | CFor c0 e c1 c2 =>
      for_sem
        (eval_com c0) (eval_r e) (eval_com c1) (eval_com c2)
  | CContinue =>
      cnt_sem
  | CBreak =>
      brk_sem
  end.



End DntSem_WhileDC.

