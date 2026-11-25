import Prop73AndTheorems

/-!
# Complete Axiom Audit for Brunn–Minkowski Inequalities for $p$-Capacity of Compact Sets

This module imports `Prop73AndTheorems` (which transitively imports the full dependency graph:
`AlexandrovConvex`, `JensenLemma`, `JLMComparison`, `EnvelopePerturbation`, `NonlinearEnvelope`,
and the upstream capacity/Green/regularity library) and prints the exact axiom dependencies of
every main theorem.

All theorems must depend only on the standard Lean 4 / Mathlib axioms:
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx` and zero custom axioms.
-/

-- Foundational convex & viscosity analysis
#print axioms BMCompactPDE.alexandrov_convex_lipschitz
#print axioms BMCompactPDE.jensen_lemma_exists_good_maximizer
#print axioms BMCompactPDE.envelope_jensen_exists_good_maximizer

-- General Lemma 3.7 / Lemma 3.6 (JLM viscosity comparison for all 1 < p < ∞, n ≥ 2)
#print axioms BMCompactPDE.WeakPHarmonicPair.forced_family_W1p_tendsto_allp_gen
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.viscosity_le_allp
#print axioms BMCompactPDE.WeakPHarmonicPair.viscosity_le_allp

-- General Lemma 7.2 / Lemma 4.7 (nonlinear sup-min envelope is viscosity p-subsolution, all 1 < p < ∞, n ≥ 2)
#print axioms BMCompactPDE.viscosity_supConvolution_of_subsolutions
#print axioms BMCompactPDE.weak_viscosity_supConvolution_subcritical_allp
#print axioms BMCompactPDE.weak_viscosity_supConvolution_atBot_allp

-- Proposition 7.3 / Proposition 4.8 & General Theorems A(a), A(c), B(c), C(a), C(b), C(c)
#print axioms BMCompactPDE.ContinuousUnitCapacityData.envelope_le_allp
#print axioms BMCompactPDE.ContinuousUnitCapacityData.min_le_allp
#print axioms BMCompactPDE.IsExteriorGreen.green_max_comparison_allp
#print axioms BMCompactPDE.theoremA_subcritical_allp
#print axioms BMCompactPDE.theoremA_supercritical_allp
#print axioms BMCompactPDE.theoremB_critical_allp
#print axioms BMCompactPDE.theoremC_subcritical_outer_allp
#print axioms BMCompactPDE.theoremC_critical_outer_allp
