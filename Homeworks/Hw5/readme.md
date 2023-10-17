# My Analysis for 0926 assignment problem 3


* I think you have to define {} to have the highest priority, otherwise for `IF E THEN IF E THEN S ELSE S ELSE S`, without bracing to become `IF E THEN { IF E THEN S ELSE S} ELSE S`, you will run into a problem here: `IF E THEN (IF E THEN S)| ELSE S ELSE S`.

* Although this step is not ambiguous when we look at it, we know that it is ultimately illegal if `IF E THEN S` reduces, but it is bound to do so due to priority, right? I remember the program itself will not look that far, it should just look at:
  1. If you want to reduce, then it is because it is not feasible to move the next character to the left side of the line instead of the reduce.
  2.  If you want to move, then it is because if you reduce, there is no next symbol in the follow set of the symbols that you get from the reduce that is being moved into the line.

* But here `IF E THEN IF E THEN S ｜ ELSE S ELSE S`, the reduce is to look at the closest left side of the line, but it seems that the left side of the line is not feasible after just moving into `ELSE` without taking the reduce. 

* If it is to be moved in, it seems that there is nothing to say that the reduce of `IF E THEN (IF E THEN S)` is changed into `IF E THEN (S) ｜ ELSE` and then move into ELSE is not feasible.

* So, there's a move to a reduce conflict here, but if you add that priority of `IF E THEN S > IF E THEN S ELSE S`, it seems to imply that I must reduce `IF E THEN S` in this case. But that would result in `S ELSE S ELSE S` not being legal anymore, whereas the string itself `IF E THEN IF E THEN S ELSE S ELSE S` has a legal interpretation. So my idea is that `IF E THEN S ELSE S` has a higher priority than `IF E THEN S`, and then `{}` has the highest priority. Because if you specify the priority this way, `IF E THEN {IF E THEN S} ELSE S`, without `{}`, it doesn't really get the same semantics as with `{}`, but it can be legitimately construed as a non-terminator at the end. The reason for considering `{}` is so that both meanings can be expressed:
  1. `IF E THEN {IF E THEN S} ELSE S`
  2. `IF E THEN {IF E THEN S ELSE S}`


# Operator Binding

Operator binding refers to the direction in which operators of the same priority are organised in an expression, i.e. the order in which an object is bound to an operator when the operators on both sides of the object are of the same priority, C specifies the direction in which the various operators are bound (binding).

Most of the combining direction is "from left to right", i.e., left first, then right, e.g., a- b+c, there are two operators on both sides of b with the same priority, b combines with minus first, performs the operation of a- b, and then performs the operation of adding c.



# Note From TA

这次9月26日的书面作业最后一题if then else这道题还是有部分同学做错。这里解释一下：这道题大部分错的同学思路还是对的，就是优先看有没有可以配对的if then else，如果没有再让if then配对，或者指明规约规则间优先使用顺序，但是这样类似的说法不够程序化，不能直接作为解决方案，所以我们统一按照做错处理。一般我们给语法解析器额外加的规则只能是：    （1）某两个终结符之间的优先级的先后顺序。    （2）某个终结符的结合性是左结合还是右结合；终结符的结合性和优先级的定义如下：    （1）优先级规定了一个符号左右两侧出现 不同 符号时该如何结合。        符号 E 和 F 之间的优先级关系决定了遇到 ... E X | F ... 这种结构时解析器的行为：        如果 E 优先级高于 F，则优先对现有结构进行规约；如果 E 优先级低于 F，则优先将符号 F 移入。    （2）结合性规定了一个符号左右两侧出现 优先级相同 符号时该如何结合。        符号 E 和 F 的结合性决定了遇到 ... E X | F ... 这种结构且 E 和 F 的优先级相同时解析器的行为：        如果都是左结合，则优先对现有结构进行规约；如果都是右结合，则优先将符号 E 移入；否则有冲突。        （*）事实上，在Bison里同一优先级只能规定一种结合性。    题目中的冲突显然是由 THEN 和 ELSE 两个不同的终结符导致的，所以应该通过规定两者间的优先级来解决。此时，解决方法有（1）使 ELSE 优先级高于 THEN，这样解析器会根据上述定义（1）优先将 ELSE 移入进行if then else规则的规约。（2）使 ELSE 和 THEN 同优先级，且 ELSE 和 THEN 都是右结合，这样解析器会根据上述定义（2）优先将 ELSE 移入进行if then else规则的规约。错误的解决方案：THEN 优先级高于 ELSE，或者同优先级但是都是左结合，会导致解析器贪心的将所有 IF、THEN 规约完成，导致末尾会剩下许多 ELSE 无法移入，无法对任何 if then else 语句进行规约。
