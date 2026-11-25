import RootLocalContinuousGradient
import WeakUniqueness

/-! Identify a continuous actual distributional gradient with the classical
C1 gradient pointwise. C1 is an input here, not a new nonlinear regularity
claim; linear PDE regularity constructs this input separately. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

theorem HasWeakGradientOn.eqOn_classical_gradient_of_continuous
    {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hg : HasWeakGradientOn Ω u g) (hΩ : IsOpen Ω)
    (hC1 : ContDiffOn ℝ 1 u Ω) (hgc : ContinuousOn g Ω) :
    EqOn g (gradient u) Ω := by
  have hclassic := hasWeakGradientOn_of_contDiffOn_one hΩ hC1
  have hc := continuousOn_gradient_of_contDiffOn_one hΩ hC1
  have he := hg.ae_unique hclassic hΩ
    (hgc.locallyIntegrableOn hΩ.measurableSet) (hc.locallyIntegrableOn hΩ.measurableSet)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he hΩ hgc hc

end BMCompactPDE
#print axioms BMCompactPDE.HasWeakGradientOn.eqOn_classical_gradient_of_continuous
