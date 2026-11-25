import GradientHessianNaturalLocal
import UpstreamGradientScalarEmbedding

/-! Genuine first higher-integrability gain for the gradient in dimension two.
The actual weak PDE constructs natural-gradient Sobolev rows; the actual
critical scalar embedding gives L4 for those rows, hence L^(2p) for the raw
weak-gradient field. No higher integrability or scalar/gradient continuity is
an input. This is not a full Moser iteration or C1 theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_two_natural_norm_zero
    {p : ℝ} (hp : 2≤p) (v : Space 2) :
    ‖naturalGradientMap p 0 v‖=‖v‖^(p/2) := by
  rw [naturalGradientMap,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  norm_num only [zero_pow,zero_add]
  rw [←Real.rpow_two,←Real.rpow_mul (norm_nonneg v)]
  have he : 2*((p-2)/4)=(p/2+1)-2 := by ring
  rw [he]
  have hh := rpow_coefficient_mul (p:=p/2+1) (by linarith) (norm_nonneg v)
  simpa only [show p/2+1-1=p/2 by ring] using hh

/-- Every actual constant-source weak solution in dimension two, for p>=2,
has its supplied weak gradient in L^(2p) on every relatively compact open
subdomain. The ambient open domain may be unbounded. -/
theorem WeakPSourcePair.memLp_gradient_first_sobolev_gain_two
    {p c : ℝ} {Ω : Set (Space 2)}
    {u : Space 2 → ℝ} {g : Space 2 → Space 2}
    (hu : WeakPSourcePair p c Ω u g) (hp : 2≤p)
    {D : Set (Space 2)} (hD : LocalDomain D Ω) :
    MemLp g (ENNReal.ofReal (2*p)) (volume.restrict D) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hD.2.2
  let U : Set (Space 2) := thickening δ (closure D)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening δ (closure D)).trans hthick
  have hDU : LocalDomain D U :=
    ⟨hD.1,hD.2.1,self_subset_thickening hδ (closure D)⟩
  obtain ⟨H,hH⟩ := hu.exists_local_naturalGradient_sobolev_rows hp (by decide : 2≤2) hU
  have hV : MemLp (fun x => naturalGradientMap p 0 (g x)) (ENNReal.ofReal 4)
      (volume.restrict D) := by
    apply memLp_piLp_iff.mpr
    intro i
    simpa only [Nat.cast_ofNat,show (2:ℝ)*2=4 by norm_num] using!
      (hH i).memLp_local_twice_dimension hU.1 (by decide : 2≤2) (by norm_num) hDU
  have hgMeas := (hu.2.2.1 D hD).2.2.1.1
  have hhalf : 0<p/2 := by linarith
  have he : ENNReal.ofReal (2*p)/ENNReal.ofReal (p/2)=ENNReal.ofReal 4 := by
    rw [←ENNReal.ofReal_div_of_pos hhalf]
    congr 1
    field_simp
    norm_num
  apply (memLp_norm_rpow_iff (p:=ENNReal.ofReal (2*p)) (q:=ENNReal.ofReal (p/2))
    hgMeas (ENNReal.ofReal_ne_zero_iff.mpr hhalf) ENNReal.ofReal_ne_top).mp
  simpa only [he,ENNReal.toReal_ofReal hhalf.le,upstream_two_natural_norm_zero hp] using! hV.norm

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.memLp_gradient_first_sobolev_gain_two
