# Assignment 1129

1. F
2. F

3. T
4. T
5. T

6. T. 反证法: 如果存在 $s_1 ，s_2$  s.t. $\left(s_1, s_2\right) \in [[ c_1]] ，\left(s_1, s_2\right) \notin [[ c_2 ]]$ 

   1. case 1: 从 $s_1$ 状态出发， $c_2$ 终止. 令 $\mathrm{P}=\left\{s=s_1\right\}, \mathrm{Q}=\left\{s=s_2\right\}$. 则 $\{\mathrm{P}\} c_1\{\mathrm{Q}\}$ 成立，但是 $\{\mathrm{P}\} c_2\{\mathrm{Q}\}$ 不成立与题目条件矛盾 
   2. case 2: 从 $s_1$ 状态出发， $c_2$ 不终止. 令 $\mathrm{P}=\left\{s=s_1\right\}, \mathrm{Q}=\left\{s \neq s_2\right\}$. 则 $\{\mathrm{P}\} c_1\{\mathrm{Q}\}$ 不成立，但是 $\{\mathrm{P}\} c_2\{\mathrm{Q}\}$ 成立与题目条件矛盾
7. F
8. T. False无法作为循环不变量，因为循环前条件无法推出False；True可以作为循环不变量，因为其可以被前条件推出，循环过程中保持不变，且循环后条件总成立。

9. `y <= 2x`

   1. 前条件能推出 P
   2. 循环体能保持循环不变量
   3. `y <= 2x && x < y` 能推出后条件。
10. `P: n(n-1)/2 <= m && s <= n(n+1)/2`

    1. 前条件能推出 P
    2. 循环体能保持循环不变量
    3. ` n(n-1)/2 <= m && s <= n(n+1)/2 && m < s` 能推出后条件
11. `x = n && n >= i * i`

    1. 前条件能推出 P

    2. 循环体能保持循环不变量

    3. `x = n && n >= i * i && (x < (i + 1) * (i + 1))`能推出后条件

12. $\exist x', 0 = x$  && $x'+y+z \ge 100$ && $x'\le 0$

13. $\exist x', x' + y = x$  && $0 <= x' + y <= 100$ && $x' * y <= 100$

14. $\exist y',\exists x', x - y' = y$  && $ x' == m$ && $y' == n$ && $x == x' + n$

    