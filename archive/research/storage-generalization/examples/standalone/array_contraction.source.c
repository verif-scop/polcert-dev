for (t = 1; t <= T; t++)
  for (i = 0; i < N; i++)
    A[t][i] = A[t - 1][i] + 1;
