# Brunn–Minkowski Inequalities for $p$-Capacity of Compact Sets (Lean 4)

A complete, zero-`sorry`, axiom-audited Lean 4 formalization of the main Brunn–Minkowski and potential-comparison theorems from:

> *Brunn–Minkowski inequality for $p$-capacity of compact sets* ([https://arxiv.org/abs/2610.28421](https://arxiv.org/abs/2610.28421))

All main theorems are proved for **all exponents $1 < p < \infty$** and **all dimensions $n \ge 2$** using only the standard Lean 4 / Mathlib axioms (`[propext, Classical.choice, Quot.sound]`), with **zero `sorry`s** and **zero custom axioms**.

---

## Main Formalized Theorems

> *Note on numbering:* In `BM_Compact_Final.tex`, the LaTeX labels `lem3.7`, `lem7.2`, and `prop7.3` render in the compiled PDF as **Lemma 3.6**, **Lemma 4.7**, and **Proposition 4.8**, respectively. Both numbers are listed below for clarity.

| Paper Result | Regime | Lean Declaration | Module |
| :--- | :--- | :--- | :--- |
| **Theorem A (a)** — Brunn–Minkowski for $\mathrm{Cap}_p$ | $1 < p < n$, $n \ge 2$ | `BMCompactPDE.theoremA_subcritical_allp` | `Prop73AndTheorems.lean` |
| **Theorem A (c)** — Brunn–Minkowski for supercritical $\mathcal{C}_p$ | $p > n \ge 2$ | `BMCompactPDE.theoremA_supercritical_allp` | `Prop73AndTheorems.lean` |
| **Theorem B (c)** — Brunn–Minkowski for critical outer capacity $\bar{\mathcal{C}}_n$ | $p = n \ge 2$ | `BMCompactPDE.theoremB_critical_allp` | `Prop73AndTheorems.lean` |
| **Theorem C (a)** — Pointwise capacitary / Green comparison ($p$-regular sets) | $1 < p < \infty$, $n \ge 2$ | `BMCompactPDE.ContinuousUnitCapacityData.min_le_allp`, `BMCompactPDE.IsExteriorGreen.green_max_comparison_allp` | `Prop73AndTheorems.lean` |
| **Theorem C (b)** — Outer capacitary limit & l.s.c. regularization comparison | $1 < p < n$, $n \ge 2$ | `BMCompactPDE.theoremC_subcritical_outer_allp` | `Prop73AndTheorems.lean` |
| **Theorem C (c)** — Outer Green's function limit comparison | $p = n \ge 2$ | `BMCompactPDE.theoremC_critical_outer_allp` | `Prop73AndTheorems.lean` |
| **Proposition 4.8** (`\label{prop7.3}`) — Envelope comparison $w^* \le w$ | $1 < p < \infty$, $n \ge 2$ | `BMCompactPDE.ContinuousUnitCapacityData.envelope_le_allp`, `BMCompactPDE.IsExteriorGreen.green_max_comparison_allp` | `Prop73AndTheorems.lean` |
| **Lemma 4.7** (`\label{lem7.2}`) — Sup-min convolution is a viscosity $p$-subsolution | $1 < p < \infty$, $n \ge 2$ | `BMCompactPDE.viscosity_supConvolution_of_subsolutions`, `BMCompactPDE.weak_viscosity_supConvolution_subcritical_allp`, `BMCompactPDE.weak_viscosity_supConvolution_atBot_allp` | `NonlinearEnvelope.lean` |
| **Lemma 3.6** (`\label{lem3.7}`) — JLM viscosity comparison principle | $1 < p < \infty$, $n \ge 2$ | `BMCompactPDE.WeakPHarmonicPair.viscosity_le_allp`, `BMCompactPDE.WeakPSourceSupersolutionPair.viscosity_le_allp` | `JLMComparison.lean` |
| **Alexandrov's Theorem** — a.e. second-order Taylor expansion of convex Lipschitz functions | $n \ge 1$ | `BMCompactPDE.alexandrov_convex_lipschitz` | `AlexandrovConvex.lean` |
| **Jensen's Lemma** — local perturbed maximizers with full-measure contact | $n \ge 2$ | `BMCompactPDE.jensen_lemma_exists_good_maximizer`, `BMCompactPDE.envelope_jensen_exists_good_maximizer` | `JensenLemma.lean`, `EnvelopePerturbation.lean` |

---

## Proof Architecture (Nonlinear Comparison & Viscosity Stack)

Building on the 317-module upstream PDE, Sobolev, potential-theory, Green's-function, and capacity-reduction library, the nonlinear viscosity comparison and sup-min envelope machinery is organized into 11 modular files plus a top-level axiom audit:

1. `LipschitzNull.lean` — Lipschitz maps send AddHaar-null sets to AddHaar-null sets.
2. `AlexandrovConvex.lean` — Alexandrov's theorem (a.e. twice differentiability of convex Lipschitz functions) proved from Rademacher's theorem and the Minty resolvent.
3. `SupInfConv.lean` — Sup-convolution regularity, semiconvexity, uniform approximation, and viscosity $p$-subsolution preservation.
4. `TaylorViscosity.lean` — Punctual second-order Taylor viscosity sub/supersolution inequalities for the normalized $p$-Laplacian.
5. `C2Semiconvex.lean` — Local semiconvexity of $C^2$ functions and uniform continuity of the classical $p$-Laplacian.
6. `JensenLemma.lean` — Local Jensen's lemma for semiconvex functions.
7. `JLMComparison.lean` — Juutinen–Lindqvist–Manfredi (JLM) viscosity comparison principle (**Lemma 3.6** / `\label{lem3.7}`) for all $1 < p < \infty$, $n \ge 2$.
8. `TaylorEnvelopeContact.lean` — Punctual second-order Taylor envelope contact comparison for the normalized $p$-Laplacian.
9. `EnvelopePerturbation.lean` — Joint perturbation & Jensen contact lemma for the sup-min envelope.
10. `NonlinearEnvelope.lean` — Proof that the sup-min envelope is a viscosity $p$-subsolution (**Lemma 4.7** / `\label{lem7.2}`) for all $1 < p < \infty$, $n \ge 2$.
11. `Prop73AndTheorems.lean` — End-to-end assembly of **Proposition 4.8** (`\label{prop7.3}`) and **Theorems A(a), A(c), B(c), C(a), C(b), C(c)**.
12. `AxiomAudit.lean` — Single-entry `#print axioms` verification for every main theorem.

---

## Building and Verifying

### Toolchain
- **Lean 4:** `leanprover/lean4:v4.33.1` (pinned in `lean-toolchain`)
- **Mathlib 4:** commit `0df444a360eaa60ab8c11dca51a86af692955474` (pinned in `lakefile.lean` and `lake-manifest.json`)

### Quick Verification
```bash
# 1. Fetch prebuilt Mathlib oleans (recommended)
lake exe cache get

# 2. Build the main theorems and run the complete axiom audit
lake build AxiomAudit
```

Or build the entire 329-module library:
```bash
lake build
```

When `lake build AxiomAudit` completes, every `#print axioms` line reports only:
```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## License

MIT License (see `LICENSE`).
