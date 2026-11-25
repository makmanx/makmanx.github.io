import BMCompactChecked
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Genuine smooth multiplication of arbitrary distributional Sobolev pairs.
The input function need not have any classical differentiability. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem gradient_fun_mul_actual {n : ℕ} {f h : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    gradient (fun y => f y * h y) x = f x • gradient h x + h x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hh]
  simp only [map_add,map_smul]

theorem continuous_gradient_of_contDiff_one {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  exact continuousOn_univ.mp
    (continuousOn_gradient_of_contDiffOn_one isOpen_univ hf.contDiffOn)

/-- The actual distributional product rule, proved using the genuine product
test χφ and Hölder integrability; no chain-rule premise is supplied. -/
theorem SobolevPair.weakGradient_mul_smooth {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) {χ : Space n → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    HasWeakGradientOn Ω (fun x => χ x * u x)
      (fun x => χ x • g x + u x • gradient χ x) := by
  letI := (holderConjugate_p_dual hu.1).symm
  intro φ hφ i
  have hχd := hχ.differentiable (by simp)
  have hφd := hφ.1.differentiable (by simp)
  have htest : SmoothTest Ω (fun x => χ x * φ x) :=
    ⟨hχ.mul hφ.1,hφ.2.1.mul_left,tsupport_mul_subset_right.trans hφ.2.2⟩
  obtain ⟨hi,hj,he⟩ := hu.2.2.2 _ htest i
  let A : Space n → ℝ := fun x => χ x*u x*gradient φ x i
  let B : Space n → ℝ := fun x => u x*gradient χ x i*φ x
  let C : Space n → ℝ := fun x => χ x*g x i*φ x
  have hc : Continuous (fun x => gradient χ x i) :=
    (EuclideanSpace.proj i).continuous.comp
      (continuous_gradient_of_contDiff_one (hχ.of_le (by simp)))
  have hβ : MemLp (fun x => gradient χ x i*φ x)
      (ENNReal.ofReal (p/(p-1))) (volume.restrict Ω) :=
    ((hc.mul hφ.1.continuous).memLp_of_hasCompactSupport hφ.2.1.mul_left).restrict Ω
  have hB : Integrable B (volume.restrict Ω) := by
    simpa only [B,Pi.mul_apply,mul_assoc] using! hu.2.1.integrable_mul hβ
  have hL : (fun x => u x*gradient (fun y => χ y*φ y) x i) = A+B := by
    funext x
    rw [gradient_fun_mul_actual (hχd x) (hφd x)]
    simp only [A,B,Pi.add_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  have hR : (fun x => g x i*(χ x*φ x)) = C := by
    funext x
    dsimp only [C]
    ring
  rw [hL] at hi he
  rw [hR] at hj he
  have hA : Integrable A (volume.restrict Ω) := by
    convert! hi.sub hB using 1
    funext x
    simp only [Pi.sub_apply,Pi.add_apply,add_sub_cancel_right]
  have hG : (fun x => (χ x • g x+u x • gradient χ x) i*φ x) = C+B := by
    funext x
    simp only [C,B,Pi.add_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  refine ⟨hA,?_,?_⟩
  · rw [hG]
    exact hj.add hB
  · change (∫ x in Ω, A x) = _
    rw [hG]
    change (∫ x in Ω, A x) = -(∫ x in Ω, C x+B x)
    rw [integral_add hj hB]
    change (∫ x in Ω, A x+B x) = -(∫ x in Ω, C x) at he
    rw [integral_add hA hB] at he
    linarith

theorem SobolevPair.mul_smooth_compactSupport {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) {χ : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    SobolevPair p Ω (fun x => χ x*u x)
      (fun x => χ x • g x+u x • gradient χ x) := by
  have hχtop : MemLp χ (∞ : ℝ≥0∞) (volume.restrict Ω) :=
    hχ.continuous.memLp_top_of_hasCompactSupport hχc _
  have hgradtop : MemLp (gradient χ) (∞ : ℝ≥0∞) (volume.restrict Ω) :=
    (continuous_gradient_of_contDiff_one (hχ.of_le (by simp))).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hχc) _
  refine ⟨hu.1,?_,?_,hu.weakGradient_mul_smooth hχ⟩
  · exact hu.2.1.mul' hχtop
  · exact (hu.2.2.1.smul hχtop).add (hgradtop.smul hu.2.1)

end BMCompactPDE
#print axioms BMCompactPDE.gradient_fun_mul_actual
#print axioms BMCompactPDE.continuous_gradient_of_contDiff_one
#print axioms BMCompactPDE.SobolevPair.weakGradient_mul_smooth
#print axioms BMCompactPDE.SobolevPair.mul_smooth_compactSupport
