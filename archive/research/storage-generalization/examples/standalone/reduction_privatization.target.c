for (p = 0; p < P; p++) {
  local[p] = 0;
  for (i in chunk(p))
    local[p] += A[i];
}
sum = 0;
for (p = 0; p < P; p++)
  sum += local[p];
