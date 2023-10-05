struct S {
  int x;
  char y;
};

struct S p;
struct S * p;
struct S * (* f)(int, struct S *);
struct S * (* g)();
char * (* h)(int * (*)(int, int), struct S *);
