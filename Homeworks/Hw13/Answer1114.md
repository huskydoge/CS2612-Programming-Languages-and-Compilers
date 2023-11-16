# Assignment 1114

## Problem 1

```
n = 10;
i = 0;
LABEL_1:
	if(! i < n)
	then {#1 = i < n}
	else {
		#2 = i * 8
		#3 = p + #2
		#4 = * #3
		#1 = (#4 != 0)
	};
	if(! #1)
	then {jmp LABEL_2}
	else {
		i = i + 1
	};
	jmp LABEL_1
LABEL_2:
	.....
```

## Problem 2

```
BB:
	x = 10
	jmp BB_PRE

BB_PRE:
	if (x > 0)
	then {jmp BB_BODY}
	else {jmp BB_NEXT};

BB_BODY:
	x = x - 1
	jmp BB_PRE
	
BB_NEXT:
	y = x
	jmp END_INFO
```

## Problem 3

```
u: #2 = read_int()
def(u) = #2
use(u) = 

in(u) = 
out(u) = #2
```

```
u: #4 = 0
def(u) = #4
use(u) = 

in(u) = #2
out(u) = #2, #4
```

```
u: jmp 1 
def(u) = 
use(u) = 

in(u) = #2, #4
out(u) = #2, #4
```

```
u: if (NE(#2, 0)) then jmp 2 else jmp 3 
def(u) = 
use(u) = #2

in(u) = # 2, #4
out(u) = #2, #4
```

```
u: #7 = DEREF(#2)
def(u) = #7
use(u) = #2

in(u) = #2, #4
out(u) = #4, #7, #2
```

```
u: #4 = PLUS(#4, #7)
def(u) = #4
use(u) = #4, #7

in(u) = #4, #7, #2
out(u) = #2, #4
```

```
u: #8 = PLUS(#2, 8)
def(u) = #8
use(u) = #2

in(u) = #2, #4
out(u) = #8, #4
```

```
u: #2 = DEREF(#8)
def(u) = #2
use(u) = #8

in(u) = #8, #4
out(u) = #2, #4
```

```
u: jmp 1
def(u) = 
use(u) = 

in(u) = #2, #4
out(u) = #2, #4
```

## Problem 4

```
u: #3 = 0
def(u) = #3
use(u) = 

in(u) = 
out(u) = #3
```

```
u: #2 = read_int() 
def(u) = #2
use(u) = 

in(u) = #3
out(u) = #2, #3
```

```
u: jmp 1
def(u) = 
use(u) = 

in(u) = #2, #3
out(u) = #2, #3
```

```
u: if (NE(#2, 0)) then jmp 2 else jmp 3
def(u) = 
use(u) = #2

in(u) = #2, #3
out(u) = #2, #3
```

```
u: #7 = #2
def(u) = #7
use(u) = #2

in(u) = #2, #3
out(u) = #2, #3, #7
```

```
u: #8 = PLUS(#2, 8)
def(u) = #8
use(u) = #2

in(u) = #2, #3, #7
out(u) = #8, #7, #3
```

```
u: #2 = DEREF(#8)
def(u) = #2
use(u) = #8

in(u) = #8, #7, #3
out(u) = #7, #3, #2
```

```
u: #9 = PLUS(#7, 8)
def(u) = #9
use(u) = #7

in(u) = #7, #3, #2
out(u) = #3, #9, #7, #2
```

```
u: * #9 = #3
def(u) = 
use(u) = #3, #9

in(u) = #3, #9, #7, #2
out(u) = #7, #2
```

```
u: #3 = #7
def(u) = #3
use(u) = #7

in(u) = #7, #2
out(u) = #2, #3
```

```
u: jmp 1
def(u) = 
use(u) = 

in(u) = #2, #3
out(u) = #2, #3
```

