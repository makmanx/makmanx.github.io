import BMCompactChecked
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Actual mollification commutes with the distributional gradient. The input
has no classical derivative hypothesis. The whole-space Sobolev graph and
genuine smooth compact kernels are used directly, without selected multi-index
derivatives or a prior commutation premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution
namespace BMCompactPDE

theorem scalar_convolution_comm_actual {n : ℕ} (f h : Space n → ℝ) :
    f ⋆[lsmul ℝ ℝ,volume] h = h ⋆[lsmul ℝ ℝ,volume] f := by
  funext x
  rw [convolution_lsmul_swap]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => mul_comm (f (x-y)) (h y))

theorem gradient_comp_const_sub_actual {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (a x : Space n) :
    gradient (fun y => f (a-y)) x = -gradient f (a-x) := by
  have hd : HasFDerivAt (fun y : Space n => f (a-y))
      (-(fderiv ℝ f (a-x))) x := by
    convert! (hf (a-x)).hasFDerivAt.comp x
      ((hasFDerivAt_const a x).sub (hasFDerivAt_id x)) using 1 <;> simp
  unfold gradient
  rw [hd.fderiv]
  simp only [map_neg]

theorem gradient_scalar_convolution_coordinate {n : ℕ}
    {u ρ : Space n → ℝ} (hu : LocallyIntegrable u volume)
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) (x : Space n) (i : Fin n) :
    gradient (ρ ⋆[lsmul ℝ ℝ,volume] u) x i =
      ∫ y, u y*gradient ρ (x-y) i := by
  let e : Space n := EuclideanSpace.basisFun (Fin n) ℝ i
  have hd := hc.hasFDerivAt_convolution_right (μ := volume)
    (lsmul ℝ ℝ) hu (hρ.of_le (by simp)) x
  rw [scalar_convolution_comm_actual ρ u,gradient_coordinate_eq_fderiv,hd.fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hc.fderiv ℝ)
      (hρ.continuous_fderiv (by simp))]
  simp only [convolution,lsmul_apply,smul_eq_mul,gradient_coordinate_eq_fderiv]

/-- For an actual arbitrary Sobolev pair on the whole space, the classical
gradient of its genuine mollification is the mollified actual weak field. -/
theorem SobolevPair.gradient_convolution_eq {n : ℕ} {p : ℝ}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) {ρ : Space n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) :
    gradient (ρ ⋆[lsmul ℝ ℝ,volume] u) = ρ ⋆[lsmul ℝ ℝ,volume] g := by
  have hp : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hu.1.le
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa using hu.2.1
  have hgm : MemLp g (ENNReal.ofReal p) volume := by simpa using hu.2.2.1
  have hul := hum.locallyIntegrable hp
  have hρd := hρ.differentiable (by simp)
  funext x
  apply PiLp.ext
  intro i
  let ψ : Space n → ℝ := fun y => ρ (x-y)
  have hψ : SmoothTest univ ψ := by
    refine ⟨hρ.comp (contDiff_const.sub contDiff_id),?_,subset_univ _⟩
    simpa only [ψ,Function.comp_def,Homeomorph.trans_apply,
      Homeomorph.coe_addLeft,Homeomorph.coe_neg,sub_eq_add_neg] using
      hc.comp_homeomorph ((Homeomorph.neg (Space n)).trans (Homeomorph.addLeft x))
  have he := (hu.2.2.2 ψ hψ i).2.2
  simp only [Measure.restrict_univ] at he
  have hgψ (y : Space n) : gradient ψ y i = -gradient ρ (x-y) i := by
    simpa only [ψ,PiLp.neg_apply] using congrArg (fun z : Space n => z i)
      (gradient_comp_const_sub_actual hρd x y)
  simp only [hgψ,mul_neg,integral_neg] at he
  have he' := neg_injective he
  rw [gradient_scalar_convolution_coordinate hul hρ hc]
  rw [convolution,eval_integral_piLp]
  · change (∫ y, u y*gradient ρ (x-y) i) = ∫ y, ρ y*g (x-y) i
    rw [he']
    have hswap := convolution_lsmul_swap (f := ρ) (g := fun y => g y i)
      (μ := volume) (x := x)
    change (∫ y, g y i*ρ (x-y)) = _
    simpa only [convolution,lsmul_apply,smul_eq_mul,mul_comm] using hswap.symm
  · intro j
    exact (hc.convolutionExists_left (lsmul ℝ ℝ) hρ.continuous
      ((memLp_coordinate hgm j).locallyIntegrable hp) x).integrable

end BMCompactPDE
#print axioms BMCompactPDE.scalar_convolution_comm_actual
#print axioms BMCompactPDE.gradient_comp_const_sub_actual
#print axioms BMCompactPDE.gradient_scalar_convolution_coordinate
#print axioms BMCompactPDE.SobolevPair.gradient_convolution_eq
