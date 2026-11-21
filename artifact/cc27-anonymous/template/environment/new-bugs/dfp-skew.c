/* Pluto --dfp: skewing removes the strict satisfaction of a dependence.
 * polycc dfp-skew.c --dfp --notile --noparallel
 * Expected output: 0 (A[2][1][1] receives the 0 written by S2(2,2)).   */
#include <stdio.h>
#define N 5
#define M 4
static unsigned A[10][9][11];
int main(void) {
  int i, j;
  for (int x = 0; x < 10; x++) for (int y = 0; y < 9; y++) for (int z = 0; z < 11; z++)
    A[x][y][z] = 100 + x * 99 + y * 11 + z;
#pragma scop
  for (i = 0; i < N; i++)
    for (j = 2; j < M; j++) {
      A[i][1][1] = A[j][j + 1][N - i + 4];   /* S1 */
      A[j + i - 1][i + 2][j + 5] = 0;        /* S2 */
    }
#pragma endscop
  printf("%u\n", A[2][1][1]);
  return 0;
}
