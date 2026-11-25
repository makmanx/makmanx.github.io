import RegCaccioppoli
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Actual smooth integer-power cutoff calculus. This file does not assume a
chain rule for the weak solution; only the cutoff itself is differentiated. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ContDiff Topology ENNReal
namespace BMCompactPDE

theorem gradient_natPow_cutoff {n : ℕ} {η : Space n → ℝ}
    (hη : Differentiable ℝ η) (M : ℕ) (x : Space n) :
    gradient (fun y => η y^M) x = ((M : ℝ)*η x^(M-1)) • gradient η x := by
  unfold gradient
  rw [((hη x).hasFDerivAt.pow M).fderiv]
  simp only [map_smul,nsmul_eq_mul]

theorem SmoothTest.natPow_cutoff {n M : ℕ} {D : Set (Space n)}
    {η : Space n → ℝ} (hη : SmoothTest D η) (hM : M ≠ 0) :
    SmoothTest D (fun x => η x^M) := by
  have hz : (0 : ℝ)^M=0 := zero_pow hM
  refine ⟨hη.1.pow M,hη.2.1.comp_left hz,?_⟩
  exact (tsupport_comp_subset hz η).trans hη.2.2

end BMCompactPDE
#print axioms BMCompactPDE.gradient_natPow_cutoff
#print axioms BMCompactPDE.SmoothTest.natPow_cutoff
