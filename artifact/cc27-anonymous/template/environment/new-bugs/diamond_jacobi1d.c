#include <stdio.h>
#define T 2
#define N 6
static long a[N], b[N];
int main(void) {
  int t, i;
  for (i = 0; i < N; i++) { a[i] = i * 7 % 13; b[i] = 0; }
#pragma scop
  for (t = 0; t < T; t++) {
    for (i = 1; i < N - 1; i++)
      b[i] = a[i - 1] + a[i] + a[i + 1];
    for (i = 1; i < N - 1; i++)
      a[i] = b[i];
  }
#pragma endscop
  for (i = 0; i < N; i++) printf("a[%d]=%ld b[%d]=%ld\n", i, a[i], i, b[i]);
  return 0;
}
