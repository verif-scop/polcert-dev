#include <omp.h>

#define S1(i)	a = 0;
#define S2(i)	b[i] = a;

		int t1, t2;

	int lb, ub, lbp, ubp, lb2, ub2;
	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 0) {
  for (t1=0;t1<=N;t1++) {
    S1(t1);
    S2(t1);
  }
}
/* End of CLooG code */
