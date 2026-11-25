import TouchingDerivative

/-! Full gradient assertion of printed Lemma4.2(a), source equation5.9. -/
noncomputable section
set_option autoImplicit false
open Filter Set InnerProductSpace
open scoped Topology
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- First derivatives at a touching pair are positively parallel. -/
theorem touching_gradient_positive_proportional {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x g₁ g₂ g : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : HasGradientAt v₁ g₁ y) (h₂ : HasGradientAt v₂ g₂ z)
    (hφ : HasGradientAt φ g x) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ g = α • g₁ ∧ g = β • g₂ ∧
      t * α + (1-t) * β = 1 := by
  have hL₁ : toDual ℝ E g₁ ≠ 0 := by
    intro h
    apply hg₁
    apply (toDual ℝ E).injective
    simpa using h
  have hL₂ : toDual ℝ E g₂ ≠ 0 := by
    intro h
    apply hg₂
    apply (toDual ℝ E).injective
    simpa using h
  obtain ⟨α,β,hα,hβ,hA,hB,hnorm⟩ := touching_fderiv_positive_proportional ht ht1
    hx h₁.hasFDerivAt h₂.hasFDerivAt hφ.hasFDerivAt hL₁ hL₂ hv₁ hv₂ htouch
  refine ⟨α,β,hα,hβ,?_,?_,hnorm⟩
  · apply (toDual ℝ E).injective
    simpa only [map_smul] using hA
  · apply (toDual ℝ E).injective
    simpa only [map_smul] using hB

omit [CompleteSpace E] in
/-- Convert positive proportionality into the source's common unit normal and
harmonic reciprocal identity. All parameters are constructed, not assumed. -/
theorem unit_normal_of_positive_proportional {t α β : ℝ} {g₁ g₂ g : E}
    (hα : 0 < α) (hβ : 0 < β) (hg₁ : g₁ ≠ 0)
    (hA : g = α • g₁) (hB : g = β • g₂)
    (hnorm : t * α + (1-t) * β = 1) :
    ∃ (ν : E) (a b d : ℝ), ‖ν‖ = 1 ∧ 0 < a ∧ 0 < b ∧ 0 < d ∧
      g₁ = (-a) • ν ∧ g₂ = (-b) • ν ∧ g = (-d) • ν ∧
      1 / d = t / a + (1-t) / b := by
  let a : ℝ := ‖g₁‖
  have ha : 0 < a := norm_pos_iff.mpr hg₁
  let ν : E := (-a⁻¹) • g₁
  let b : ℝ := (α / β) * a
  let d : ℝ := α * a
  have hb : 0 < b := mul_pos (div_pos hα hβ) ha
  have hd : 0 < d := mul_pos hα ha
  have hν : ‖ν‖ = 1 := by
    change ‖(-a⁻¹) • g₁‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr ha)]
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha.ne'
  have he₁ : g₁ = (-a) • ν := by
    dsimp only [ν]
    rw [smul_smul]
    have hm : (-a) * (-a⁻¹) = 1 := by field_simp
    rw [hm, one_smul]
  have hg₂ : g₂ = (α / β) • g₁ := by
    calc
      g₂ = β⁻¹ • (β • g₂) := (inv_smul_smul₀ hβ.ne' g₂).symm
      _ = β⁻¹ • g := by rw [← hB]
      _ = (α / β) • g₁ := by rw [hA, smul_smul]; congr 1; ring
  refine ⟨ν,a,b,d,hν,ha,hb,hd,he₁,?_,?_,?_⟩
  · rw [hg₂, he₁, smul_smul]
    congr 1
    dsimp [b]
    ring
  · rw [hA, he₁, smul_smul]
    congr 1
    dsimp [d]
    ring
  · have had : α = d / a := by dsimp [d]; field_simp
    have hbd : β = d / b := by dsimp [d,b]; field_simp
    have hs : t * (d / a) + (1-t) * (d / b) = 1 := by
      rw [← had, ← hbd]
      exact hnorm
    calc
      1 / d = (t * (d / a) + (1-t) * (d / b)) / d := by rw [hs]
      _ = t / a + (1-t) / b := by field_simp

/-- The exact differentiable-gradient conclusion in source Lemma4.2(a).
The local touching hypothesis is in the equivalent product-neighbourhood form. -/
theorem local_touching_gradient_harmonic_relation {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : DifferentiableAt ℝ v₁ y) (h₂ : DifferentiableAt ℝ v₂ z)
    (hφ : DifferentiableAt ℝ φ x)
    (hg₁ : gradient v₁ y ≠ 0) (hg₂ : gradient v₂ z ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∃ (ν : E) (a b d : ℝ), ‖ν‖ = 1 ∧ 0 < a ∧ 0 < b ∧ 0 < d ∧
      gradient v₁ y = (-a) • ν ∧ gradient v₂ z = (-b) • ν ∧
      gradient φ x = (-d) • ν ∧ 1 / d = t / a + (1-t) / b := by
  obtain ⟨α,β,hα,hβ,hA,hB,hnorm⟩ := touching_gradient_positive_proportional ht ht1
    hx h₁.hasGradientAt h₂.hasGradientAt hφ.hasGradientAt hg₁ hg₂ hv₁ hv₂ htouch
  exact unit_normal_of_positive_proportional hα hβ hg₁ hA hB hnorm

end BMCompactAnalytic
#print axioms BMCompactAnalytic.touching_gradient_positive_proportional
#print axioms BMCompactAnalytic.unit_normal_of_positive_proportional
#print axioms BMCompactAnalytic.local_touching_gradient_harmonic_relation
