#ifndef LIB_H_INCLUDED
#define LIB_H_INCLUDED

#define NONE 4294967295

unsigned int build_nat(char * c, int len);
char * new_str(char * str, int len);
struct SLL_hash_table;
struct SLL_hash_table * init_SLL_hash();
long long SLL_hash_get(struct SLL_hash_table * t, char * key);
void SLL_hash_set(struct SLL_hash_table * t, char * key, long long value);
void SLL_hash_delete(struct SLL_hash_table * t, char * key);

#endif
