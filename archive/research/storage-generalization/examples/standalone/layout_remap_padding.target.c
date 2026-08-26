double A_pad[N][M + 1];
#define A_LOG(i, j) A_pad[i][j]
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A_LOG(i, j) + 1;
