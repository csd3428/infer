void create_null_path_ok(int* p) {
  if (p) {
    *p = 32;
  }
}
void call_create_null_path_then_deref_unconditionally_ok(int* p) {
  create_null_path_ok(p);
  *p = 52;
}
void create_null_path2_ok(int* p) {
  int* q = ((void *)0);
  if (p) {
    *p = 32;
  }
  *p = 52;
}
void malloc_then_call_create_null_path_then_deref_unconditionally_latent(
    int* p) {
  int* x = (int*)malloc(sizeof(int));
  if (p) {
    *p = 32;
  }
  create_null_path_ok(p);
  *p = 52;
  free(x);
}
void nullptr_deref_young_bad(int* x) {
  int* vec[65] = {x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, ((void *)0)};
  int p = *vec[64];
}
void FN_nullptr_deref_old_bad(int* x) {
  int* vec[65] = {((void *)0), x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x, x,
                  x, x, x, x, x, x, x, x, x, x, x, x, x, x};
  int p = *vec[0];
}
void malloc_free_ok() {
  int* p = (int*)malloc(sizeof(int));
  free(p);
}
void wrap_free(void* p) { free(p); }
void interproc_free_ok() {
  int* p = (int*)malloc(sizeof(int));
  wrap_free(p);
}
_Noreturn void no_return();
void wrap_malloc(int** x) {
  *x = (int*)malloc(sizeof(int));
  if (!*x) {
    no_return();
  }
}
void call_no_return_good() {
  int* x = ((void *)0);
  wrap_malloc(&x);
  *x = 5;
  free(x);
}
void FN_bug_after_malloc_result_test_bad(int* x) {
  x = (int*)malloc(sizeof(int));
  if (x) {
    int* y = ((void *)0);
    *y = 42;
  }
}
