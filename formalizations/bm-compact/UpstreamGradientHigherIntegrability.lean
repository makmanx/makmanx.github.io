import GradientHessianNaturalLocal
import PotentialSobolevBoost

/-! A genuine first Sobolev gain for the gradient of an actual nonlinear weak
solution. The natural-gradient W1,2 rows are constructed from the weak PDE;
a constructed smooth compact cutoff and actual W0 embedding give the larger
gradient exponent. No higher integrability or pointwise gradient bound is input.
This does not prove gradient continuity, C1, or a complete Moser iteration. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_natural_norm_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 2≤p) (v : E) :
    ‖naturalGradientMap p 0 v‖=‖v‖^(p/2) := by
  rw [naturalGradientMap,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  norm_num only [zero_pow,zero_add]
  rw [←Real.rpow_two,←Real.rpow_mul (norm_nonneg v)]
  have he : 2*((p-2)/4)=(p/2+1)-2 := by ring
  rw [he]
  have hh := rpow_coefficient_mul (p:=p/2+1) (by linarith) (norm_nonneg v)
  simpa only [show p/2+1-1=p/2 by ring] using hh

private theorem upstream_local_critical_memLp
    {n : ℕ} {U D : Set (Space n)}
    {v : Space n → ℝ} {H : Space n → Space n}
    (hv : SobolevPair 2 U v H) (hU : IsOpen U) (hD : LocalDomain D U)
    (hn : 3≤n) :
    MemLp v (ENNReal.ofReal ((n:ℝ)*2/((n:ℝ)-2))) (volume.restrict D) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU hD.2.2
  let χ : Space n → ℝ := fun x => Real.smoothTransition (a x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp ha.1
  have hχc : HasCompactSupport χ := ha.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ)))
  have hχs : tsupport χ⊆U :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))) a).trans ha.2.2.1
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (ha.2.2.2 x (subset_closure hx))
  have hz := hv.mul_smooth_compactSupport_zeroBoundary hU hχ hχc hχs
  have hnR : (2:ℝ)<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 2<3) hn)
  have hboost := (hz.critical_sobolev_explicit hnR).1
  have hd := hboost.mono_measure (Measure.restrict_mono_set volume
    (subset_closure.trans hD.2.2))
  apply hd.ae_eq
  filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
  simp only [hχ1 x hx,one_mul]

/-- Actual local gradient higher integrability at the first Sobolev exponent.
The natural-gradient derivatives, cutoff, zero-boundary approximation and
Sobolev gain are all derived. The ambient domain can be unbounded. -/
theorem WeakPSourcePair.memLp_gradient_first_sobolev_gain
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hp : 2≤p) (hn : 3≤n)
    {D : Set (Space n)} (hD : LocalDomain D Ω) :
    MemLp g (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-2))) (volume.restrict D) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hD.2.2
  let U : Set (Space n) := thickening δ (closure D)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening δ (closure D)).trans hthick
  have hDU : LocalDomain D U :=
    ⟨hD.1,hD.2.1,self_subset_thickening hδ (closure D)⟩
  have hn2 : 2≤n := (by decide : 2≤3).trans hn
  obtain ⟨H,hH⟩ := hu.exists_local_naturalGradient_sobolev_rows hp hn2 hU
  have hV : MemLp (fun x => naturalGradientMap p 0 (g x))
      (ENNReal.ofReal ((n:ℝ)*2/((n:ℝ)-2))) (volume.restrict D) := by
    apply memLp_piLp_iff.mpr
    intro i
    exact upstream_local_critical_memLp (hH i) hU.1 hDU hn
  have hgMeas := (hu.2.2.1 D hD).2.2.1.1
  have hhalf : 0<p/2 := by linarith
  have hnR : (2:ℝ)<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 2<3) hn)
  have he : ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-2))/ENNReal.ofReal (p/2)=
      ENNReal.ofReal ((n:ℝ)*2/((n:ℝ)-2)) := by
    rw [←ENNReal.ofReal_div_of_pos hhalf]
    congr 1
    field_simp
  apply (memLp_norm_rpow_iff (p:=ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-2)))
    (q:=ENNReal.ofReal (p/2)) hgMeas (ENNReal.ofReal_ne_zero_iff.mpr hhalf)
      ENNReal.ofReal_ne_top).mp
  simpa only [he,ENNReal.toReal_ofReal hhalf.le,upstream_natural_norm_zero hp] using! hV.norm

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.memLp_gradient_first_sobolev_gain
