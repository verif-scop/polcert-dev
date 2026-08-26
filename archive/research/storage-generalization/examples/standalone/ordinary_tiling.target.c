for (ii = 0; ii < N; ii += T)
  for (jj = 0; jj < M; jj += T)
    for (i = ii; i < min(ii + T, N); i++)
      for (j = jj; j < min(jj + T, M); j++)
        B[i][j] = A[i][j] + 1;
