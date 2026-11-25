import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
The exact linear first-variation consequence of the local touching condition in
BM_Compact_Final.tex, printed Lemma4.2(a), source eqn5.11--eqn5.13.
No nonlinear PDE or gradient alignment is postulated.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped InnerProductSpace
namespace BMCompactAnalytic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem touching_linear_equal_levels {t : ℝ} (L L₁ L₂ : E →ₗ[ℝ] ℝ)
    (h : ∀ u v, min (L₁ u) (L₂ v) ≤ L (t • u + (1-t) • v))
    {u v : E} (heq : L₁ u = L₂ v) :
    L (t • u + (1-t) • v) = L₁ u := by
  have hp := h u v
  have hm := h (-u) (-v)
  simp only [map_add, map_smul, smul_eq_mul] at hp hm ⊢
  simp only [map_neg, ← heq, min_self] at hp hm
  linarith

private theorem exists_linear_value_one (L : E →ₗ[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ u : E, L u = 1 := by
  have hex : ∃ u : E, L u ≠ 0 := by
    by_contra! hn
    apply hL
    ext u
    exact hn u
  obtain ⟨u, hu⟩ := hex
  refine ⟨(L u)⁻¹ • u, ?_⟩
  simp [hu]

/-- The min-touching first variation forces positive parallel linear
functionals, with the exact weighted reciprocal relation. -/
theorem touching_linear_positive_proportional {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (L L₁ L₂ : E →ₗ[ℝ] ℝ) (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0)
    (h : ∀ u v, min (L₁ u) (L₂ v) ≤ L (t • u + (1-t) • v)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ L = a • L₁ ∧ L = b • L₂ ∧
      t * a + (1-t) * b = 1 := by
  obtain ⟨e₁, he₁⟩ := exists_linear_value_one L₁ hL₁
  obtain ⟨e₂, he₂⟩ := exists_linear_value_one L₂ hL₂
  have hnorm := touching_linear_equal_levels L L₁ L₂ h (u := e₁) (v := e₂)
    (he₁.trans he₂.symm)
  simp only [map_add, map_smul, smul_eq_mul, he₁] at hnorm
  have hprop₁ (u : E) : L u = L e₁ * L₁ u := by
    have heq : L₁ u = L₂ ((L₁ u) • e₂) := by simp [he₂]
    have hh := touching_linear_equal_levels L L₁ L₂ h heq
    simp only [map_add, map_smul, smul_eq_mul] at hh
    apply mul_left_cancel₀ ht.ne'
    have hm := congrArg (fun r : ℝ => r * L₁ u) hnorm
    nlinarith only [hh, hm]
  have hprop₂ (v : E) : L v = L e₂ * L₂ v := by
    have heq : L₁ ((L₂ v) • e₁) = L₂ v := by simp [he₁]
    have hh := touching_linear_equal_levels L L₁ L₂ h heq
    simp only [map_add, map_smul, smul_eq_mul, he₁] at hh
    apply mul_left_cancel₀ (sub_pos.mpr ht1).ne'
    have hm := congrArg (fun r : ℝ => r * L₂ v) hnorm
    nlinarith only [hh, hm]
  have ha : 0 ≤ L e₁ := by
    have hh := h e₁ 0
    simp only [he₁, map_zero, min_eq_right zero_le_one, smul_zero, add_zero,
      map_smul, smul_eq_mul] at hh
    nlinarith
  have hb : 0 ≤ L e₂ := by
    have hh := h 0 e₂
    simp only [he₂, map_zero, min_eq_left zero_le_one, smul_zero, zero_add,
      map_smul, smul_eq_mul] at hh
    nlinarith
  have ha' : 0 < L e₁ := by
    by_contra! hn
    have hz : L e₁ = 0 := le_antisymm hn ha
    have he₂zero : L e₂ = 0 := by simpa [hz] using hprop₁ e₂
    rw [hz, he₂zero] at hnorm
    norm_num at hnorm
  have hb' : 0 < L e₂ := by
    by_contra! hn
    have hz : L e₂ = 0 := le_antisymm hn hb
    have he₁zero : L e₁ = 0 := by simpa [hz] using hprop₂ e₁
    rw [hz, he₁zero] at hnorm
    norm_num at hnorm
  refine ⟨L e₁, L e₂, ha', hb', ?_, ?_, hnorm⟩
  · ext u
    exact hprop₁ u
  · ext v
    exact hprop₂ v

end BMCompactAnalytic

#print axioms BMCompactAnalytic.touching_linear_equal_levels
#print axioms BMCompactAnalytic.touching_linear_positive_proportional
