for (t = 1; t <= T; t++)
  for (i = 0; i < N; i++)
    A2[t % 2][i] = A2[(t - 1) % 2][i] + 1;
