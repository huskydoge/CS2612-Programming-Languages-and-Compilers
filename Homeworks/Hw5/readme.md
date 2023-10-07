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




