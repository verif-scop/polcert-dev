# Third-Party Material

The supplement preserves third-party authorship, copyright notices, licenses,
and background citations.

| Component | Location | License or attribution source |
| --- | --- | --- |
| CompCert-derived infrastructure | `source/common`, `source/cfrontend`, `source/cparser`, `source/lib`, architecture directories | File headers and `source/LICENSE` |
| Verified Polyhedra Library (VPL) | `source/VPL` | `source/VPL/LICENSE` and source headers |
| Flocq | `source/flocq` | Source headers and `licenses/LGPL-3.0.txt` |
| MenhirLib | `source/MenhirLib` | Source headers and `licenses/LGPL-3.0.txt` |
| Pluto and its pinned dependencies | `third_party/pluto` | License and attribution files in each source archive |
| Pluto-derived test inputs | `source/tests`, `evidence/rejected-optimizer-outputs`, `evidence/optimized-loop-examples` | Pluto benchmark corpus; `licenses/Pluto-MIT.txt` |
| Other external benchmark samples | `source/tests` | Source comments and local provenance records where supplied |

PolCert is distributed under the GNU Lesser General Public License version 2.1
or, where stated in source headers, any later version. The top-level `LICENSE`
is copied from the validated PolCert source snapshot. Components with different
licenses retain their applicable text under `source/` or `licenses/`.
