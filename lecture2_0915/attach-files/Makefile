all: main

lang.o: lang.c lang.h
	gcc -c lang.c

lexer.c: lang.l
	flex lang.l

lexer.o: lexer.c lang.h
	gcc -c lexer.c

main.o: main.c lang.h lexer.c
	gcc -c main.c

main: main.o lang.o lexer.o
	gcc main.o lang.o lexer.o -o main

clean:
	rm -f *.o lexer.c lexer.h main

%.c: %.l
