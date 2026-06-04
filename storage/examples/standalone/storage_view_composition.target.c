for (i = 0; i < N; i++) {
  Apad[2 * i] = A[i];       /* layout projection source -> mid */
  tmp[i] = Apad[2 * i] + 1; /* private-erasure target -> mid */
  B[i] = tmp[i];
}

