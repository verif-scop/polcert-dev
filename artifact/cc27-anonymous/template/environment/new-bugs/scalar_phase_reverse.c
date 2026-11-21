#include <stdio.h>
#define T 2
#define N 33
static long A[T][N], B[T][N];
int main(void) {
  int i, j;
  for (i = 0; i < T; i++)
    for (j = 0; j < N; j++) { A[i][j] = (i * 7 + j * 3) % 11; B[i][j] = 0; }
#pragma scop
  for (i = 1; i < T; i++) {
    for (j = 0; j < N; j++)
      A[i][j] = A[i - 1][j] + 1;
    for (j = 0; j < N; j++)
      B[i][j] = A[i][N - 1 - j];
  }
#pragma endscop
  for (i = 0; i < T; i++)
    for (j = 0; j < N; j++) printf("A[%d][%d]=%ld B[%d][%d]=%ld\n", i, j, A[i][j], i, j, B[i][j]);
  return 0;
}
