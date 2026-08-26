for (t = 0; t < T; t++)
  for (i = 0; i < N; i++) {
    X_exp[t][i] = t + i;
    Y[t][i] = X_exp[t][i];
  }
for (i = 0; i < N; i++)
  X[i] = X_exp[T - 1][i];
