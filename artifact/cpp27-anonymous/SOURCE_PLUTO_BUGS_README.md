# Pluto Reliability Cases

These directories contain minimized optimizer outputs used to check PolCert's
validation boundaries. Four cases reproduce silent miscompilations in the
audited official Pluto revision, one exercises an unsafe optional control
interface, one records a development-fork regression, and one checks
raw-to-canonical parallel-hint mapping without claiming a Pluto defect.

Each case README explains the violated dependence or transformation condition
and PolCert's response. The reviewer-facing table, recorded results, and
bug-report draft are under
`../../../evidence/optimizer-reliability/`, relative to this README.

Run the source tests with:

```sh
opam exec -- make test-pluto-bugs
```
