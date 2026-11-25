import Mathlib.Order.CompleteLattice.Basic

/-!
The order-theoretic passage to outer limits in Theorem C(b),(c),
BM_Compact_Final.tex, proof at lines 1952-1967. The PDE comparison for each
approximating neighbourhood remains an explicit hypothesis here. This file
does not assert that the envelopes are capacitary or Green functions.
-/
set_option autoImplicit false

namespace BMCompactPDE

/-- Infimum envelopes preserve the common-index minimum comparison. -/
theorem min_comparison_iInf {ι X α : Type*} [CompleteLinearOrder α]
    (combine : X → X → X) (U V W : ι → X → α)
    (h : ∀ i y z, min (U i y) (V i z) ≤ W i (combine y z)) (y z : X) :
    min (⨅ i, U i y) (⨅ i, V i z) ≤ ⨅ i, W i (combine y z) := by
  apply le_iInf
  intro i
  exact (inf_le_inf (iInf_le (fun j => U j y) i)
    (iInf_le (fun j => V j z) i)).trans (h i y z)

/-- Supremum envelopes preserve the common-index maximum comparison,
including extended-real values. -/
theorem max_comparison_iSup {ι X α : Type*} [CompleteLinearOrder α]
    (combine : X → X → X) (U V W : ι → X → α)
    (h : ∀ i y z, W i (combine y z) ≤ max (U i y) (V i z)) (y z : X) :
    (⨆ i, W i (combine y z)) ≤ max (⨆ i, U i y) (⨆ i, V i z) := by
  apply iSup_le
  intro i
  exact (h i y z).trans (sup_le_sup (le_iSup (fun j => U j y) i)
    (le_iSup (fun j => V j z) i))

end BMCompactPDE

#print axioms BMCompactPDE.min_comparison_iInf
#print axioms BMCompactPDE.max_comparison_iSup
