import SmoothWeakBridge

/-! The local classical-to-distributional bridge, valid without global
smoothness across a boundary or a singular point outside the domain. -/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem hasWeakGradientOn_of_contDiffOn {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    HasWeakGradientOn Ω u (gradient u) := by
  intro φ hφ i
  let v : Space n := EuclideanSpace.basisFun (Fin n) ℝ i
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.1.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hφd : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    hφ.2.1.fderiv_apply ℝ v
  have hsupport₁ : tsupport (fun x => u x * fderiv ℝ φ x v) ⊆ Ω :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hφ.2.2)
  have hsupport₂ : tsupport (fun x => fderiv ℝ u x v * φ x) ⊆ Ω :=
    tsupport_mul_subset_right.trans hφ.2.2
  have hsupport₃ : tsupport (fun x => u x * φ x) ⊆ Ω :=
    tsupport_mul_subset_right.trans hφ.2.2
  have hc₁ : Continuous (fun x => u x * fderiv ℝ φ x v) :=
    (hu.continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ hsupport₁
  have hc₂ : Continuous (fun x => fderiv ℝ u x v * φ x) :=
    (hdu.mul hφ.1.continuous.continuousOn).continuous_of_tsupport_subset hΩ hsupport₂
  have hc₃ : Continuous (fun x => u x * φ x) :=
    (hu.continuousOn.mul hφ.1.continuous.continuousOn).continuous_of_tsupport_subset hΩ hsupport₃
  have h₁ : Integrable (fun x => u x * fderiv ℝ φ x v) volume :=
    hc₁.integrable_of_hasCompactSupport hφd.mul_left
  have h₂ : Integrable (fun x => fderiv ℝ u x v * φ x) volume :=
    hc₂.integrable_of_hasCompactSupport hφ.2.1.mul_left
  have h₃ : Integrable (fun x => u x * φ x) volume :=
    hc₃.integrable_of_hasCompactSupport hφ.2.1.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    h₂ h₁ h₃
    (fun x hx => (hu.contDiffAt (hΩ.mem_nhds (hφ.2.2 hx))).differentiableAt (by simp))
    (fun x _ => hφ.1.differentiable (by simp) x)
  have hφzero : ∀ x, x ∉ Ω → φ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))
  have hdφzero : ∀ x, x ∉ Ω → fderiv ℝ φ x v = 0 := by
    intro x hx
    have hx' : x ∉ tsupport (fun y => fderiv ℝ φ y v) :=
      fun ht => hx (hφ.2.2 ((tsupport_fderiv_apply_subset ℝ v) ht))
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : Space n => fderiv ℝ φ y v) hx'
  have hleft : (∫ x in Ω, u x * fderiv ℝ φ x v) =
      ∫ x, u x * fderiv ℝ φ x v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hdφzero x hx])
  have hright : (∫ x in Ω, fderiv ℝ u x v * φ x) =
      ∫ x, fderiv ℝ u x v * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hφzero x hx])
  simp only [gradient_coordinate_eq_fderiv]
  exact ⟨h₁.restrict, h₂.restrict, by rw [hleft, hright]; exact hibp⟩

end BMCompactPDE

#print axioms BMCompactPDE.hasWeakGradientOn_of_contDiffOn
