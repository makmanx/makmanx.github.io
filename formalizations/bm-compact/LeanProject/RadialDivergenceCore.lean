import RadialFoundation
import Mathlib.LinearAlgebra.Trace

noncomputable section
set_option autoImplicit false
open InnerProductSpace Filter Topology
open scoped InnerProductSpace

namespace BMCompactPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The classical divergence, defined as the trace of the actual Fréchet derivative. -/
def classicalDivergence (V : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ V x).toLinearMap

/-- The normalized radial flux appearing after source equation (2.7). -/
def radialSourceFlux (n : ℕ) (σ : ℝ) (x : E) : E :=
  (σ⁻¹ * ‖x‖ ^ (-(n : ℝ))) • x

theorem hasFDerivAt_norm_rpow_smul (q : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖ ^ q • y)
      (‖x‖ ^ q • ContinuousLinearMap.id ℝ E +
        ((q * ‖x‖ ^ (q - 2)) • innerSL ℝ x).smulRight x) x :=
  (hasFDerivAt_norm_rpow_nonzero q hx).smul (hasFDerivAt_id x)

section Finite
variable [FiniteDimensional ℝ E]

theorem classicalDivergence_norm_rpow_smul (q : ℝ) {x : E} (hx : x ≠ 0) :
    classicalDivergence (fun y : E => ‖y‖ ^ q • y) x =
      ((Module.finrank ℝ E : ℝ) + q) * ‖x‖ ^ q := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold classicalDivergence
  rw [(hasFDerivAt_norm_rpow_smul q hx).fderiv]
  change LinearMap.trace ℝ E
    (‖x‖ ^ q • LinearMap.id +
      (((q * ‖x‖ ^ (q - 2)) • innerSL ℝ x).toLinearMap).smulRight x) = _
  rw [map_add, map_smul, LinearMap.trace_id, LinearMap.trace_smulRight]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_coe, coe_innerSL_apply, real_inner_self_eq_norm_sq]
  have hpow : ‖x‖ ^ (q - 2) * ‖x‖ ^ (2 : ℕ) = ‖x‖ ^ q := by
    rw [← Real.rpow_two, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    ‖x‖ ^ q * (Module.finrank ℝ E : ℝ) + (q * ‖x‖ ^ (q - 2)) * ‖x‖ ^ 2 =
        ‖x‖ ^ q * (Module.finrank ℝ E : ℝ) + q * (‖x‖ ^ (q - 2) * ‖x‖ ^ 2) := by ring
    _ = ((Module.finrank ℝ E : ℝ) + q) * ‖x‖ ^ q := by rw [hpow]; ring

theorem classicalDivergence_const_smul (a : ℝ) {V : E → E} {x : E}
    (hV : DifferentiableAt ℝ V x) :
    classicalDivergence (fun y => a • V y) x = a * classicalDivergence V x := by
  have hder : HasFDerivAt (fun y => a • V y) (a • fderiv ℝ V x) x :=
    hV.hasFDerivAt.const_smul a
  unfold classicalDivergence
  rw [hder.fderiv]
  change LinearMap.trace ℝ E (a • (fderiv ℝ V x).toLinearMap) = _
  rw [map_smul]
  rfl

/-- The source flux is divergence free at every point other than its pole. -/
theorem classicalDivergence_radialSourceFlux (n : ℕ) (σ : ℝ)
    (hdim : Module.finrank ℝ E = n) {x : E} (hx : x ≠ 0) :
    classicalDivergence (radialSourceFlux n σ : E → E) x = 0 := by
  have hf : (radialSourceFlux n σ : E → E) =
      fun y : E => σ⁻¹ • (‖y‖ ^ (-(n : ℝ)) • y) := by
    funext y
    simp [radialSourceFlux, smul_smul]
  rw [hf, classicalDivergence_const_smul σ⁻¹
    (hasFDerivAt_norm_rpow_smul (-(n : ℝ)) hx).differentiableAt,
    classicalDivergence_norm_rpow_smul (-(n : ℝ)) hx, hdim]
  simp

end Finite
end BMCompactPDE

#print axioms BMCompactPDE.classicalDivergence_norm_rpow_smul
#print axioms BMCompactPDE.classicalDivergence_radialSourceFlux
