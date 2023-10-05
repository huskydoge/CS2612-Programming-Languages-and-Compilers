struct S {
  enum {AAA, BBB, CCC} t;
  union {
    struct { void * none; } a;
    struct { } b;
    int * (* x)();
  } d;
};

struct S p;
typedef struct S SS;

typedef enum {CCCC, DDDD} E;
