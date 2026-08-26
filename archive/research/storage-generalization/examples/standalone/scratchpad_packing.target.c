for (kk = 0; kk < N; kk += T) {
  for (k = 0; k < T; k++)
    Bp[k] = B[kk + k];
  for (k = 0; k < T; k++)
    C[kk + k] = A[kk + k] + Bp[k];
}
