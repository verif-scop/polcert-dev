for (i = 0; i < N; i++) {
  local[i] = A[i];      /* copy-in boundary */
  local[i] = local[i] + 1;
  B[i] = local[i];      /* copy-out boundary */
}

