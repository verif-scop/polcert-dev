# Rejected Optimizer Outputs

Open `index.html` for the shortest case-by-case account. It states why each
proposal is invalid, what PolCert did, and where the relevant Pluto logic
resides. The recorded checks are in `results.json` and `validation.log`.

The cases have three different statuses:

| Cases | Status |
| --- | --- |
| `auto-affine-lp-cc-scaling`, `vanished-outer-parallel`, `notile-unrolljam-nonpermutable`, `tiling-innerpar-satvec` | Confirmed silent miscompilations in the checked official Pluto revision. |
| `affine-fst-reversed` | An unsafe optional control interface; this is not an automatic-scheduler witness. |
| `diamond-nointratile-reschedule` | A phase-dump fork regression, absent from official Pluto and fixed in the ordinary artifact version. |
| `matmul-parallel-hint` | A non-certifiable hint that PolCert handles conservatively; no Pluto miscompilation is claimed. |

`BUG_REPORT_DRAFT.md` contains the executable witnesses, observed wrong
results, source-level root causes, and official-version rechecks for the four
confirmed official defects and the unsafe control interface. Each case
directory contains its input and a focused explanation. Shared runners are
under `runners/`.
