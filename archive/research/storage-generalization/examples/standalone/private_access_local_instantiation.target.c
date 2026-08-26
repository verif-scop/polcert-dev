for (i = 0; i < N; i++) {
  local[f(i)] = A[i] + 1;
  B[i] = local[f(i)];
}

