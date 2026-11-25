import PotentialSobolevBoost
import Mathlib.Topology.MetricSpace.Thickening

/-! Actual local critical integrability from the concrete local Sobolev graph,
by an explicitly constructed compact cutoff and the proved critical W0 bound.
This is an integrability gain, not local boundedness, Harnack or C1 regularity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

theorem LocallySobolevPair.memLp_critical_explicit
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : LocallySobolevPair p Ω u g) (hΩ : IsOpen Ω)
    (hpn : p<(n : ℝ)) (hD : LocalDomain D Ω) :
    MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) (volume.restrict D) := by
  let K := closure D
  have hK : IsCompact K := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
  let U : Set (Space n) := thickening δ K
  have hU : LocalDomain U Ω := ⟨isOpen_thickening,hK.isBounded.thickening,
    (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  have hKU : K⊆U := self_subset_thickening hδ K
  have hDU : D⊆U := subset_closure.trans hKU
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU.1 hKU
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hs : tsupport χ⊆U :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ1 (x : Space n) (hx : x∈K) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hw := (hu U hU).mul_smooth_compactSupport_zeroBoundary hU.1 hχ hc hs
  have hb := (hw.critical_sobolev_explicit hpn).1
  have hbD := MemLp.mono_measure (Measure.restrict_mono_set volume hDU) hb
  have he : (fun x => χ x*u x) =ᵐ[volume.restrict D] u := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    change χ x*u x=u x
    rw [hχ1 x (subset_closure hx),one_mul]
  exact (memLp_congr_ae he).mp hbD

end BMCompactPDE
#print axioms BMCompactPDE.LocallySobolevPair.memLp_critical_explicit
