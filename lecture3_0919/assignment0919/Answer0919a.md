# Assignment0919a

## Problem 1

*集合对应关系：*

起始状态：{INIT, A, F}

i: {INIT, A, F} -> {D, E, J, H}

f: {D, E, J, H} -> {D, I, E, J}

\_0-9a-zA-Z: {D, I, E, J} -> {D,E,J}

\_0-9a-zA-Z:  {D,E,J} ->  {D,E,J}

\_0-9a-eg-zA-Z: {D, E, J, H} -> {D, E, J}

a-hj-zA-Z: {INIT, A, F} -> {D, E, J}

**DFA如下**：

![P1](./P1.jpeg)

## Problem 2

对应关系：

起始状态：{INIT,A,B,C}

a: {INIT, A,B,C} -> {A,B,C,D}

a: {A,B,C,D} -> {A, B,C,D} 

![P2](https://p.ipic.vip/ldgv37.jpg)

## Problem 3

对应关系：

起始状态：{INIT}

a: {INIT} -> {A,B,C,D,E,M,N}

b: {A,B,C,D,E,M,N} ->{B,C,D,E,F,M,N}

​	b:{B,C,D,E,F,M,N} -> {B,C,D,E,F,M,N} 	

​	a:{B,C,D,E,F,M,N} -> {O} 			

​	c:{B,C,D,E,F,M,N} -> {G,H,I,J} 	

​		a:{G,H,I,J} -> {K,M,N,B,C,D,E}

​			a:{K,M,N,B,C,D,E} -> {O}

​			b:{K,M,N,B,C,D,E} -> {F,M,N,B,C,D,E}		

​			c:{K,M,N,B,C,D,E} -> {G,H,I,J}

​		c:{G,H,I,J} -> {L,M,N,B,C,D,E}		

​			a: {L,M,N,B,C,D,E} -> {O}

​			b:{L,M,N,B,C,D,E}  -> {F, M, N, B, C, D, E}

​			c:{L,M,N,B,C,D,E} -> {G, H, I, J}		

c: {A,B,C,D,E,M,N} ->{G,H,I,J}

a: {A,B,C,D,E,M,N} ->{O}

![P3](https://p.ipic.vip/dgam5q.jpg)



