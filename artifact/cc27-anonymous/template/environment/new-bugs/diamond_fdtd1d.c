#include <stdio.h>
#define T 3
#define N 6
static long e[N], h[N];
int main(void) {
  int t, i;
  for (i = 0; i < N; i++) { e[i] = i * 3 % 7; h[i] = i * 5 % 11; }
#pragma scop
  for (t = 0; t < T; t++) {
    for (i = 1; i < N; i++)
      e[i] = e[i] - (h[i] - h[i - 1]);
    for (i = 0; i < N - 1; i++)
      h[i] = h[i] - (e[i + 1] - e[i]);
  }
#pragma endscop
  for (i = 0; i < N; i++) printf("e[%d]=%ld h[%d]=%ld\n", i, e[i], i, h[i]);
  return 0;
}
