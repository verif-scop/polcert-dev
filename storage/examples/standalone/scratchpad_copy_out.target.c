for (kk = 0; kk < N; kk += T) {
  for (k = 0; k < T; k++)
    Al[k] = A[kk + k];
  for (k = 0; k < T; k++)
    Al[k] = Al[k] + 1;
  for (k = 0; k < T; k++)
    A[kk + k] = Al[k];
}
