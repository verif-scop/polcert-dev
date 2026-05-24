cur[:] = A0[:];
for (t = 1; t <= T; t++) {
  for (i = 0; i < N; i++)
    next[i] = cur[i] + 1;
  swap(cur, next);
}
