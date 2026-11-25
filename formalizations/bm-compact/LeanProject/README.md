# Supporting Lean formalization for BM_Compact_Final

**Partial formalization. The manuscript's Theorems A, B and C remain unproved.**

This is the checked V11 supporting library dated 11 November 2026. It contains
255 mathematical modules (253 proof-bearing and two definition-only) and six
auxiliary audit modules. The audits cover 1,052 counted public supporting
declarations, including eight attributed existing proofs. These counts are not
percentages of manuscript coverage.

The library develops concrete distributional Sobolev pairs, weak p-Laplace
equations, comparison and capacity tools, and Green-function foundations.
Among the checked endpoints are selected interior continuous representatives
for constant-source weak solutions for every p > 1 in dimensions n >= 2,
smooth representatives for p = 2, and weak exterior Green existence for p > n
and nonempty compact sets. The last result gives a bounded canonical-profile
remainder; it does not establish a finite asymptotic constant.

General nonlinear C1/Hölder regularity, general critical-point viscosity
comparison, critical p = n Green existence, and the remaining manuscript
arguments are open in this snapshot. Later development is not included.

## Build

The source is pinned to Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. Install Lean with elan, then run
the following in a local copy of this directory:

```sh
lake exe cache get
lake build
python3 reproduce.py
```

The final command checks the frozen source hashes and import closure, rebuilds
the 261 modules in dependency order, and checks the printed axiom audits.
The accepted audit names are `propext`, `Classical.choice` and `Quot.sound`;
no `sorryAx` or custom mathematical axiom is accepted. For a quick source-only
check without Lean, run `python3 reproduce.py --check-only`.

`BMCompactUpstreamChecked.lean` imports the complete library and prints the
axioms of all 1,052 counted supporting declarations. Audit modules and build
helpers add no mathematical proof counts. Source hashes, module order and
expected audit counts are supplied alongside the code.

## Scope and provenance

The development was assisted by AI agents. A successful kernel check verifies
the formal statements and their dependencies. Matching those statements to
the manuscript remains a separate mathematical review task; the AI readback
is not independent human peer review.

This public source package contains no manuscript, reference slides, private
platform records, authentication material, cached dependencies or compiled
Lean binaries. Third-party proof attribution and license information must
accompany distribution; see the release's attribution and license files.
