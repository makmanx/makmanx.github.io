import CapacityFoundation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Basic

/-! Actual gradient-energy change of variables used in manuscript eqn4.1
and eqn9.1(c). These are statements about the concrete smooth competitors,
not assumed capacity homogeneity laws. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Pointwise

namespace BMCompactCapacityV2

def dilateTest {n : ℕ} (ρ : ℝ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  f (ρ⁻¹ • x)

def translateTest {n : ℕ} (a : Space n) (f : Space n → ℝ) (x : Space n) : ℝ :=
  f (x - a)

theorem contDiff_dilateTest {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (ρ : ℝ) : ContDiff ℝ ∞ (dilateTest ρ f) :=
  hf.comp (contDiff_id.const_smul ρ⁻¹)

theorem hasCompactSupport_dilateTest {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) {ρ : ℝ} (hρ : ρ ≠ 0) :
    HasCompactSupport (dilateTest ρ f) := by
  exact hf.comp_homeomorph (Homeomorph.smul (Units.mk0 ρ⁻¹ (inv_ne_zero hρ)))

theorem contDiff_translateTest {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : Space n) : ContDiff ℝ ∞ (translateTest a f) :=
  hf.comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_translateTest {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (a : Space n) :
    HasCompactSupport (translateTest a f) :=
  hf.comp_homeomorph (Homeomorph.subRight a)

theorem gradient_comp_const_smul {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Space n) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  have hderiv : HasFDerivAt (fun y => f (c • y))
      (c • fderiv ℝ f (c • x)) x := by
    convert! ((hf.differentiable (by simp) (c • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul c)) using 1
    ext y
    simp [ContinuousLinearMap.comp_apply, smul_apply]
  simp only [gradient, hderiv.fderiv, map_smul]

theorem gradient_translateTest {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (a x : Space n) :
    gradient (translateTest a f) x = gradient f (x - a) := by
  have hderiv : HasFDerivAt (translateTest a f) (fderiv ℝ f (x - a)) x := by
    simpa only [translateTest] using! 
      ((hasFDerivAt_comp_sub a).2 (hf.differentiable (by simp) (x - a)).hasFDerivAt)
  simp only [gradient, hderiv.fderiv]

theorem integrable_gradient_energy {n : ℕ} (p : ℝ) (hp : 0 < p)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖gradient f x‖ ^ p) volume := by
  have hcont : Continuous (fun x => ‖gradient f x‖ ^ p) :=
    (continuous_gradient_of_contDiff hf).norm.rpow_const (fun _ => Or.inr hp.le)
  have hcomp : HasCompactSupport (fun x => ‖gradient f x‖ ^ p) :=
    ((gradient_hasCompactSupport hc).comp_left (g := fun v => ‖v‖) norm_zero).rpow_const hp.ne'
  exact hcont.integrable_of_hasCompactSupport hcomp

theorem pEnergy_univ_eq_ofReal_integral {n : ℕ} (p : ℝ) (hp : 0 < p)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    pEnergy p univ f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ p) := by
  simpa only [pEnergy, Measure.restrict_univ] using
    (ofReal_integral_eq_lintegral_ofReal (integrable_gradient_energy p hp hf hc)
      (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))).symm

theorem pEnergy_dilateTest {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    pEnergy p univ (dilateTest ρ f) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * pEnergy p univ f := by
  rw [pEnergy_univ_eq_ofReal_integral p hp (contDiff_dilateTest hf ρ)
    (hasCompactSupport_dilateTest hc hρ.ne'), pEnergy_univ_eq_ofReal_integral p hp hf hc]
  have hgrad (x : Space n) : gradient (dilateTest ρ f) x =
      ρ⁻¹ • gradient f (ρ⁻¹ • x) := gradient_comp_const_smul hf _ x
  simp_rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
    Real.mul_rpow (inv_nonneg.mpr hρ.le) (norm_nonneg _)]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Space n => ‖gradient f x‖ ^ p) hρ.le]
  have hexp : ρ⁻¹ ^ p * ρ ^ Module.finrank ℝ (Space n) = ρ ^ ((n : ℝ) - p) := by
    simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
    rw [Real.rpow_sub hρ, Real.rpow_natCast, div_eq_mul_inv, Real.inv_rpow hρ.le]
    exact mul_comm _ _
  simp only [smul_eq_mul, ← mul_assoc, hexp,
    ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]

theorem pEnergy_translateTest {n : ℕ} (p : ℝ) (hp : 0 < p)
    (a : Space n) {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    pEnergy p univ (translateTest a f) = pEnergy p univ f := by
  rw [pEnergy_univ_eq_ofReal_integral p hp (contDiff_translateTest hf a)
    (hasCompactSupport_translateTest hc a), pEnergy_univ_eq_ofReal_integral p hp hf hc]
  simp_rw [gradient_translateTest hf a]
  exact congrArg ENNReal.ofReal (integral_sub_right_eq_self
    (fun x : Space n => ‖gradient f x‖ ^ p) a)

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.contDiff_dilateTest
#print axioms BMCompactCapacityV2.hasCompactSupport_dilateTest
#print axioms BMCompactCapacityV2.contDiff_translateTest
#print axioms BMCompactCapacityV2.hasCompactSupport_translateTest
#print axioms BMCompactCapacityV2.gradient_comp_const_smul
#print axioms BMCompactCapacityV2.gradient_translateTest
#print axioms BMCompactCapacityV2.integrable_gradient_energy
#print axioms BMCompactCapacityV2.pEnergy_univ_eq_ofReal_integral
#print axioms BMCompactCapacityV2.pEnergy_dilateTest
#print axioms BMCompactCapacityV2.pEnergy_translateTest
