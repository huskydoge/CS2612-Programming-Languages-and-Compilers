# Assignment0919b

1. 可能有歧义.

   `IF E THEN S ELSE S`,  若` S -> IF E THEN S`, 那么:

   `IE E THEN IF E THEN S ELSE S` 有两种解析方法：

   a.  `IE E THEN (IF E THEN S) ELSE S`

   b.  `IE E THEN (IF E THEN S ELSE S)` 也即有两种解析树。

2. 可能有歧义。考虑`*ID + ID` . （简化起见以下过程并没有完整写出转换过程）

    `E -> F -> G -> *E ->*E + F -> *ID +ID`

    `  E -> E + F -> G + F -> *E + F-> *G + F -> *ID +ID`

    存在两种不同的解析方法。

3. `ID + ID[NAT]`, 按照题中的语法可以有两种解析：

   1. `E -> E + E -> E + E[E] -> ID + ID[NAT]`
   2. `E -> E[E] -> E + E[E] -> ID + ID[NAT]`

   修改后的语法：

   ```
   F -> NAT	F -> ID		E -> E + F	F -> F[E]	
   E -> F
   ```

4. 对于 `ID + ID + ID`, 按照题中语法有两种展开方式：

    1. `E -> E + E -> E + ID -> E + E + ID -> ID + ID + ID`
    2. `E -> E + E -> ID + E -> ID + E + E -> ID + ID + ID`

    修改后的语法：

    ```
    S -> T;S		T -> ID:=E		T -> PRINT(E)		S -> T
    
    F -> NAT		F -> ID		E -> E + F		E -> F
    ```

5. 

 ```
 (a)
 E -> F
   -> F * G
   -> F * (E)
   -> F * (E + F)
   -> F * (E + G)
   -> F * (E + ID)
   -> F * (F + ID)
   -> F * (G + ID)
   -> F * (ID + ID)
   -> G * (ID + ID)
   -> (E) * (ID + ID)
   -> (E + F) * (ID + ID)
   -> (E + G) * (ID + ID)
   -> (E + ID) * (ID + ID)
   -> (F + ID) * (ID + ID)
   -> (G + ID) * (ID + ID)
   -> (ID + ID) * (ID + ID)
   
 (b)
 ID * (ID + ID) + ID
 -> G * (ID + ID) + ID
 -> F * (ID + ID) + ID
 -> F * (G + ID) + ID
 -> F * (F + ID) + ID
 -> F * (E + ID) + ID
 -> F * (E + G) + ID
 -> F * (E + F) + ID
 -> F * (E) + ID
 -> F * G + ID
 -> F + ID
 -> E + ID
 -> E + G
 -> E + F
 -> E
 
 ```

