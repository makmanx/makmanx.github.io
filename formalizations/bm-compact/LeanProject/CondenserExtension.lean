import CapacityOuterRegularity

/-!
The exact inner/outer condenser extension in the paragraph before source
eqn9.1. These are condenser capacities, not the Green/outer-Green capacities.
Compact agreement is proved, rather than assuming inner regularity of the
literal smooth-test infimum on an arbitrary open set.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace BMCompactCapacityV2

def innerCondenserCapacity {n : ℕ} (p : ℝ) (U O : Set (Space n)) : ℝ≥0∞ :=
  ⨆ (K : Set (Space n)) (_ : IsCompact K) (_ : K ⊆ U), relativeCapacity p K O

def outerCondenserCapacity {n : ℕ} (p : ℝ) (A O : Set (Space n)) : ℝ≥0∞ :=
  ⨅ (U : Set (Space n)) (_ : IsOpen U) (_ : A ⊆ U) (_ : U ⊆ O),
    innerCondenserCapacity p U O

theorem relativeCapacity_le_innerCondenserCapacity {n : ℕ} (p : ℝ)
    {K U O : Set (Space n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    relativeCapacity p K O ≤ innerCondenserCapacity p U O :=
  le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le hKU le_rfl))

theorem innerCondenserCapacity_le_relativeCapacity {n : ℕ} (p : ℝ)
    (U O : Set (Space n)) : innerCondenserCapacity p U O ≤ relativeCapacity p U O := by
  refine iSup_le fun K => iSup_le fun _ => iSup_le fun hKU => ?_
  exact relativeCapacity_mono p hKU

theorem innerCondenserCapacity_mono {n : ℕ} (p : ℝ)
    {U W O : Set (Space n)} (hUW : U ⊆ W) :
    innerCondenserCapacity p U O ≤ innerCondenserCapacity p W O := by
  refine iSup_le fun K => iSup_le fun hK => iSup_le fun hKU => ?_
  exact relativeCapacity_le_innerCondenserCapacity p hK (hKU.trans hUW)

theorem innerCondenserCapacity_mono_domain {n : ℕ} (p : ℝ) (hp : p ≠ 0)
    {U O P : Set (Space n)} (hOP : O ⊆ P) :
    innerCondenserCapacity p U P ≤ innerCondenserCapacity p U O := by
  refine iSup_le fun K => iSup_le fun hK => iSup_le fun hKU => ?_
  exact (relativeCapacity_mono_domain p hp hOP).trans
    (relativeCapacity_le_innerCondenserCapacity p hK hKU)

theorem outerCondenserCapacity_le_inner {n : ℕ} (p : ℝ)
    {A U O : Set (Space n)} (hU : IsOpen U) (hAU : A ⊆ U) (hUO : U ⊆ O) :
    outerCondenserCapacity p A O ≤ innerCondenserCapacity p U O :=
  iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hAU (iInf_le_of_le hUO le_rfl)))

theorem relativeCapacity_le_outerCondenserCapacity_of_isCompact {n : ℕ} (p : ℝ)
    {K O : Set (Space n)} (hK : IsCompact K) :
    relativeCapacity p K O ≤ outerCondenserCapacity p K O := by
  refine le_iInf fun U => le_iInf fun _ => le_iInf fun hKU => le_iInf fun _ => ?_
  exact relativeCapacity_le_innerCondenserCapacity p hK hKU

theorem outerCondenserCapacity_le_openEnlargementInf {n : ℕ} (p : ℝ)
    (A O : Set (Space n)) :
    outerCondenserCapacity p A O ≤ openEnlargementInf p A O := by
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hAU => le_iInf fun hUO => ?_
  exact (outerCondenserCapacity_le_inner p hU hAU hUO).trans
    (innerCondenserCapacity_le_relativeCapacity p U O)

/-- Agreement with source eqn2.15 for compact inputs. In particular this
applies to every compact K contained in an open condenser domain O. -/
theorem outerCondenserCapacity_eq_relativeCapacity_of_isCompact {n : ℕ}
    (p : ℝ) (hp : 0 < p) {K O : Set (Space n)} (hK : IsCompact K) :
    outerCondenserCapacity p K O = relativeCapacity p K O := by
  apply le_antisymm _ (relativeCapacity_le_outerCondenserCapacity_of_isCompact p hK)
  exact (outerCondenserCapacity_le_openEnlargementInf p K O).trans_eq
    (relativeCapacity_eq_openEnlargementInf p hp K O).symm

theorem outerCondenserCapacity_mono {n : ℕ} (p : ℝ)
    {A B O : Set (Space n)} (hAB : A ⊆ B) :
    outerCondenserCapacity p A O ≤ outerCondenserCapacity p B O := by
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hBU => le_iInf fun hUO => ?_
  exact outerCondenserCapacity_le_inner p hU (hAB.trans hBU) hUO

theorem outerCondenserCapacity_mono_domain {n : ℕ} (p : ℝ) (hp : p ≠ 0)
    {A O P : Set (Space n)} (hOP : O ⊆ P) :
    outerCondenserCapacity p A P ≤ outerCondenserCapacity p A O := by
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hAU => le_iInf fun hUO => ?_
  exact (outerCondenserCapacity_le_inner p hU hAU (hUO.trans hOP)).trans
    (innerCondenserCapacity_mono_domain p hp hOP)

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.relativeCapacity_le_innerCondenserCapacity
#print axioms BMCompactCapacityV2.innerCondenserCapacity_le_relativeCapacity
#print axioms BMCompactCapacityV2.innerCondenserCapacity_mono
#print axioms BMCompactCapacityV2.innerCondenserCapacity_mono_domain
#print axioms BMCompactCapacityV2.outerCondenserCapacity_le_inner
#print axioms BMCompactCapacityV2.relativeCapacity_le_outerCondenserCapacity_of_isCompact
#print axioms BMCompactCapacityV2.outerCondenserCapacity_le_openEnlargementInf
#print axioms BMCompactCapacityV2.outerCondenserCapacity_eq_relativeCapacity_of_isCompact
#print axioms BMCompactCapacityV2.outerCondenserCapacity_mono
#print axioms BMCompactCapacityV2.outerCondenserCapacity_mono_domain
