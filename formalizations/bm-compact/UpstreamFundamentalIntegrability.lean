import UpstreamFundamentalSphere
import CapacityFoundation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! Genuine local L1 integrability of the singular radial flux and its pairing
with actual compact smooth tests. No Sobolev membership of the potential
through its pole is inferred from these flux-integrability assertions. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem fundamental_radial_flux_measurable (n : ℕ) (σ : ℝ) :
    Measurable (radialSourceFlux n σ : Space n → Space n) := by
  exact (measurable_const.mul (measurable_norm.pow_const (-(n : ℝ)))).smul measurable_id

private theorem fundamental_radial_flux_norm_le (n : ℕ) (σ : ℝ) (x : Space n) :
    ‖radialSourceFlux n σ x‖≤|σ⁻¹| * ‖x‖^(1-(n : ℝ)) := by
  by_cases hx : x=0
  · subst x
    simpa only [radialSourceFlux,smul_zero,norm_zero] using
      (mul_nonneg (abs_nonneg σ⁻¹) (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤0) _))
  · have hr : 0<‖x‖ := norm_pos_iff.mpr hx
    rw [radialSourceFlux,norm_smul,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      |σ⁻¹| * ‖x‖^(-(n : ℝ))*‖x‖ = |σ⁻¹| * (‖x‖^(-(n : ℝ))*‖x‖^(1 : ℝ)) := by
        rw [Real.rpow_one];ring
      _ = |σ⁻¹| * ‖x‖^(1-(n : ℝ)) := by
        rw [←Real.rpow_add hr]
        congr 2
        ring
      _ ≤ _ := le_rfl

/-- The actual radial source flux belongs to L1 on every ball through the
pole. Its norm singularity is exactly of the integrable order r^(1-n). -/
theorem integrableOn_radialSourceFlux {n : ℕ} (hn : 0<n) (σ R : ℝ) :
    IntegrableOn (radialSourceFlux n σ : Space n → Space n) (ball 0 R) volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hrad : IntegrableOn (fun x : Space n => ‖x‖^(1-(n : ℝ))) (ball 0 R) volume := by
    apply (integrableOn_fun_norm_addHaar (volume : Measure (Space n))
      (f := fun r : ℝ => r^(1-(n : ℝ))) (r := R)).mpr
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 R) :=
      integrableOn_const (by simp only [Real.volume_Ioo,ENNReal.ofReal_ne_top,ne_eq,not_false_eq_true])
    refine hc.congr_fun ?_ measurableSet_Ioo
    intro r hr
    simp only [Space,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
    rw [←Real.rpow_natCast,←Real.rpow_add hr.1]
    have he : ((n-1 : ℕ) : ℝ)+(1-(n : ℝ))=0 := by
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr hn),Nat.cast_one]
      ring
    rw [he,Real.rpow_zero]
  apply (hrad.const_mul |σ⁻¹|).mono'
    (fundamental_radial_flux_measurable n σ).aestronglyMeasurable
  exact Eventually.of_forall (fundamental_radial_flux_norm_le n σ)

/-- Pairing the genuine singular radial flux with any actual compact smooth
test gradient is integrable on the whole space,including its pole. -/
theorem integrable_radialSourceFlux_gradient_test {n : ℕ} (hn : 0<n) (σ : ℝ)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => inner ℝ (radialSourceFlux n σ x) (gradient φ x)) volume := by
  have hgc := BMCompactCapacityV2.continuous_gradient_of_contDiff hφ
  have hgs := BMCompactCapacityV2.gradient_hasCompactSupport hc
  obtain ⟨R,hR0,hR⟩ := hgs.isBounded.subset_ball_lt 0 (0 : Space n)
  obtain ⟨C,hC⟩ := hgs.exists_bound_of_continuous hgc
  have hmeas : AEStronglyMeasurable
      (fun x => inner ℝ (radialSourceFlux n σ x) (gradient φ x)) volume :=
    ((fundamental_radial_flux_measurable n σ).inner hgc.measurable).aestronglyMeasurable
  have hi : IntegrableOn (fun x => inner ℝ (radialSourceFlux n σ x) (gradient φ x))
      (ball 0 R) volume := by
    apply ((integrableOn_radialSourceFlux hn σ R).norm.const_mul C).mono' hmeas.restrict
    exact Eventually.of_forall (fun x => (norm_inner_le_norm _ _).trans
      (by simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  apply hR
  apply subset_tsupport
  intro hz
  change inner ℝ (radialSourceFlux n σ x) (gradient φ x)≠0 at hx
  exact hx (by rw [hz,inner_zero_right])

end BMCompactPDE
#print axioms BMCompactPDE.integrableOn_radialSourceFlux
#print axioms BMCompactPDE.integrable_radialSourceFlux_gradient_test
