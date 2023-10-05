#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib.h"

unsigned int build_nat(char * c, int len) {
  int s = 0, i = 0;
  for (i = 0; i < len; ++i) {
    if (s > 429496729) {
      printf("We cannot handle natural numbers greater than 4294967295.\n");
      exit(0);
    }
    if (s == 429496729 && c[i] > '5') {
      printf("We cannot handle natural numbers greater than 4294967295.\n");
      exit(0);
    }
    s = s * 10 + (c[i] - '0');
  }
  return s;
}

char * new_str(char * str, int len) {
  char * res = (char *) malloc(sizeof(char) * (len + 1));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  strcpy(res, str);
  return res;
}

struct SLL_hash_cell {
  char * key;
  long long value;
  struct SLL_hash_cell * tail;
};
  
struct SLL_hash_table {
  struct SLL_hash_cell * (h[2048]);
};

unsigned int hash_fun(char * str) {
  unsigned int s = 0;
  while (str[0] != 0) {
    s = (s * 307 + 97 + str[0]) & 2047;
    str ++;
  }
  return s;
}

struct SLL_hash_table * init_SLL_hash() {
  struct SLL_hash_table * res = (struct SLL_hash_table *) malloc(sizeof(struct SLL_hash_table));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  memset(res, 0, sizeof(struct SLL_hash_table));
  return res;
}

long long SLL_hash_get(struct SLL_hash_table * t, char * key) {
  unsigned int s = hash_fun(key);
  struct SLL_hash_cell * p = t -> h[s];
  while (p != NULL) {
    if (strcmp(key, p -> key) == 0) {
      return p -> value;
    }
    p = p -> tail;
  }
  return NONE;
}

void SLL_hash_set(struct SLL_hash_table * t, char * key, long long value) {
  unsigned int s = hash_fun(key);
  struct SLL_hash_cell * * d = & (t -> h[s]);
  while ((* d) != NULL) {
    if (strcmp(key, (* d) -> key) == 0) {
      (* d) -> value = value;
      return;
    }
    d = & ((* d) -> tail);
  }
  * d = (struct SLL_hash_cell *) malloc(sizeof (struct SLL_hash_cell));
  if (* d == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  (* d) -> key = new_str(key, strlen(key));
  (* d) -> value = value;
  (* d) -> tail = NULL;
  return;
}

void SLL_hash_delete(struct SLL_hash_table * t, char * key) {
  unsigned int s = hash_fun(key);
  struct SLL_hash_cell * * d = & (t -> h[s]);
  while ((* d) != NULL) {
    if (strcmp(key, (* d) -> key) == 0) {
      struct SLL_hash_cell * p = * d;
      * d = p -> tail;
      free(p);
      return;
    }
    d = & ((* d) -> tail);
  }
}
  
