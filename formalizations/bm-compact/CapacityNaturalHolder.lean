import GradientWeightedIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Real.ConjExponents

/-! A genuine refined Holder bound retaining the small difference-field norm.
The H-weight and difference z are not combined into one coarse Lp power.
No energy bound or classical regularity is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem capacity_natural_lp_energy {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ} (hp : 0<p)
    {z : α → E} (hz : MemLp z (ENNReal.ofReal p) μ) :
    ∫ x,‖z x‖^p ∂μ=(eLpNorm z (ENNReal.ofReal p) μ).toReal^p := by
  have hI : 0≤∫ x,‖z x‖^p ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hz.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  exact (Real.rpow_inv_rpow hI hp.ne').symm

private theorem capacity_natural_integral_eq_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 1 μ) (hf0 : ∀ x,0≤f x) :
    ∫ x,f x ∂μ=(eLpNorm f 1 μ).toReal := by
  let L := hf.toLp f
  have he := L1.norm_eq_integral_norm L
  have hI : (∫ x,‖L x‖ ∂μ)=∫ x,f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,Real.norm_of_nonneg (hf0 x)]
  rw [hI] at he
  simpa only [L,Lp.norm_toLp] using he.symm

set_option maxHeartbeats 200000 in
theorem weighted_square_refined_holder_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ} (hp : 2≤p)
    {H : α → ℝ} {z : α → E} (hH0 : ∀ x,0≤H x)
    (hH : MemLp H (ENNReal.ofReal p) μ) (hz : MemLp z (ENNReal.ofReal p) μ) :
    Integrable (fun x => H x^(p-2)*‖z x‖^2) μ ∧
      (∫ x,H x^(p-2)*‖z x‖^2 ∂μ)≤
        (eLpNorm H (ENNReal.ofReal p) μ).toReal^(p-2)*
          (eLpNorm z (ENNReal.ofReal p) μ).toReal^2 := by
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hp
  rcases eq_or_lt_of_le hp with heq|hlt
  · subst p
    have hi : Integrable (fun x => ‖z x‖^2) μ := by
      simpa only [ENNReal.toReal_ofReal (show (0 : ℝ)≤2 by norm_num),Real.rpow_two] using
        hz.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num : (0 : ℝ)<2)) ENNReal.ofReal_ne_top
    have hE := capacity_natural_lp_energy (by norm_num : (0 : ℝ)<2) hz
    refine ⟨by simpa using hi,?_⟩
    simpa only [sub_self,Real.rpow_zero,one_mul,Real.rpow_two] using hE.le
  · have hm : 0<p-2 := sub_pos.mpr hlt
    let r : ℝ := p/(p-2)
    let s : ℝ := p/2
    have hrs : r.HolderConjugate s := by
      refine ⟨?_,div_pos hp0 hm,div_pos hp0 (by norm_num)⟩
      dsimp only [r,s]
      field_simp
      <;> ring
    let P := ENNReal.ofReal r
    let Q := ENNReal.ofReal s
    have : ENNReal.HolderTriple P Q 1 := by
      simpa only [P,Q] using hrs.ennrealOfReal
    let F : α → ℝ := fun x => ‖H x‖^(p-2)
    let G : α → ℝ := fun x => ‖z x‖^(2 : ℝ)
    have hF : MemLp F P μ := by
      simpa only [F,P,r,ENNReal.toReal_ofReal hm.le,←ENNReal.ofReal_div_of_pos hm]
        using hH.norm_rpow_div (ENNReal.ofReal (p-2))
    have hG : MemLp G Q μ := by
      simpa only [G,Q,s,ENNReal.toReal_ofReal (show (0 : ℝ)≤2 by norm_num),
        ←ENNReal.ofReal_div_of_pos (show (0 : ℝ)<2 by norm_num)]
        using hz.norm_rpow_div (ENNReal.ofReal 2)
    have hFG : MemLp (fun x => F x*G x) 1 μ := hG.mul' hF
    have hboundRaw := eLpNorm_smul_le_mul_eLpNorm
      (p:=P) (q:=Q) (r:=1) (μ:=μ) (f:=G) (φ:=F) hG.1 hF.1
    have hbound : eLpNorm (fun x => F x*G x) 1 μ≤eLpNorm F P μ*eLpNorm G Q μ := by
      simpa only [Pi.smul_def,Pi.mul_def,smul_eq_mul] using hboundRaw
    have hFpow : eLpNorm F P μ=(eLpNorm H (ENNReal.ofReal p) μ)^(p-2) := by
      rw [show F=(fun x => ‖H x‖^(p-2)) from rfl,eLpNorm_norm_rpow H hm]
      congr 2
      dsimp only [P,r]
      rw [←ENNReal.ofReal_mul (div_nonneg hp0.le hm.le)]
      congr 1
      field_simp
    have hGpow : eLpNorm G Q μ=(eLpNorm z (ENNReal.ofReal p) μ)^(2 : ℝ) := by
      rw [show G=(fun x => ‖z x‖^(2 : ℝ)) from rfl,eLpNorm_norm_rpow z (by norm_num)]
      congr 2
      dsimp only [Q,s]
      rw [←ENNReal.ofReal_mul (div_nonneg hp0.le (by norm_num : (0 : ℝ)≤2))]
      congr 1
      ring
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hF.2.ne hG.2.ne) hbound
    rw [hFpow,hGpow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,←ENNReal.toReal_rpow,Real.rpow_two] at hreal
    have hEq : (fun x => F x*G x)=(fun x => H x^(p-2)*‖z x‖^2) := by
      funext x
      simp only [F,G,Real.norm_eq_abs,abs_of_nonneg (hH0 x),Real.rpow_two]
    refine ⟨by simpa only [hEq] using memLp_one_iff_integrable.mp hFG,?_⟩
    have hInt := capacity_natural_integral_eq_norm hFG (fun x =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
    rw [←hInt,hEq] at hreal
    exact hreal

end BMCompactPDE
#print axioms BMCompactPDE.weighted_square_refined_holder_bound
