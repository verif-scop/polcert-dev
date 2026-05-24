for (ii = 1; ii < N - 1; ii += T) {
  l = ii; r = min(ii + T, N - 1);
  for (i = max(1, l - H); i < min(N - 1, r + H); i++)
    Local[i] = A[i - 1] + A[i] + A[i + 1];
  for (i = l; i < r; i++)
    B[i] = Local[i];
}
