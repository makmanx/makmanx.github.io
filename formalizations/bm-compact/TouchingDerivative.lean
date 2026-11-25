import TouchingLinear
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Lattice

/-!
The actual derivative bridge for printed Lemma4.2(a), equation5.11.
The universal inequality between derivatives is proved by right-hand
difference quotients from the local touching inequality; it is not assumed.
-/
noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace BMCompactAnalytic

/-- A local minimum comparison with equal values gives the minimum bound
for the right-hand first derivatives, using actual derivative limits. -/
theorem min_le_derivative_of_local_min_comparison
    {f₁ f₂ f : ℝ → ℝ} {a b c : ℝ}
    (h₁ : HasDerivAt f₁ a 0) (h₂ : HasDerivAt f₂ b 0) (hf : HasDerivAt f c 0)
    (hv₁ : f₁ 0 = f 0) (hv₂ : f₂ 0 = f 0)
    (hcomp : ∀ᶠ r in 𝓝 (0 : ℝ), min (f₁ r) (f₂ r) ≤ f r) :
    min a b ≤ c := by
  have hA : Tendsto (fun r : ℝ => (f₁ r - f₁ 0) / r)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      h₁.tendsto_slope_zero_right
  have hB : Tendsto (fun r : ℝ => (f₂ r - f₂ 0) / r)
      (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      h₂.tendsto_slope_zero_right
  have hC : Tendsto (fun r : ℝ => (f r - f 0) / r)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hf.tendsto_slope_zero_right
  apply le_of_tendsto_of_tendsto (hA.min hB) hC
  filter_upwards [hcomp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hpos
  rw [hv₁, hv₂, min_div_div_right hpos.le, min_sub_sub_right]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hr (f 0)) hpos.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equation5.11 for the actual Frechet derivatives at a local touching pair. -/
theorem touching_first_variation {t : ℝ} {v₁ v₂ φ : E → ℝ} {y z x : E}
    {L₁ L₂ L : E →L[ℝ] ℝ}
    (hx : x = t • y + (1-t) • z)
    (h₁ : HasFDerivAt v₁ L₁ y) (h₂ : HasFDerivAt v₂ L₂ z)
    (hφ : HasFDerivAt φ L x)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∀ u v : E, min (L₁ u) (L₂ v) ≤ L (t • u + (1-t) • v) := by
  intro u v
  have hpath₁ : HasDerivAt (fun r : ℝ => y + r • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y
  have hpath₂ : HasDerivAt (fun r : ℝ => z + r • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hpath : HasDerivAt
      (fun r : ℝ => t • (y + r • u) + (1-t) • (z + r • v))
      (t • u + (1-t) • v) 0 :=
    (hpath₁.const_smul t).add (hpath₂.const_smul (1-t))
  have hd₁ : HasDerivAt (fun r : ℝ => v₁ (y + r • u)) (L₁ u) 0 := by
    simpa only [Function.comp_apply] using!
      h₁.comp_hasDerivAt_of_eq 0 hpath₁ (by simp)
  have hd₂ : HasDerivAt (fun r : ℝ => v₂ (z + r • v)) (L₂ v) 0 := by
    simpa only [Function.comp_apply] using!
      h₂.comp_hasDerivAt_of_eq 0 hpath₂ (by simp)
  have hdφ : HasDerivAt
      (fun r : ℝ => φ (t • (y + r • u) + (1-t) • (z + r • v)))
      (L (t • u + (1-t) • v)) 0 := by
    simpa only [Function.comp_apply] using!
      hφ.comp_hasDerivAt_of_eq 0 hpath (by simpa using hx)
  have hevent : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
      min (v₁ (y + r • u)) (v₂ (z + r • v)) ≤
        φ (t • (y + r • u) + (1-t) • (z + r • v)) := by
    have hp : Tendsto (fun r : ℝ => (y + r • u,z + r • v))
        (𝓝 (0 : ℝ)) (𝓝 (y,z)) := by
      simpa using hpath₁.continuousAt.tendsto.prodMk_nhds hpath₂.continuousAt.tendsto
    exact hp.eventually htouch
  exact min_le_derivative_of_local_min_comparison hd₁ hd₂ hdφ
    (by simpa [← hx] using hv₁) (by simpa [← hx] using hv₂) hevent

/-- Full first-order proportionality consequence of the actual local touching
hypotheses. The positive weights and reciprocal normalization are conclusions. -/
theorem touching_fderiv_positive_proportional {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {L₁ L₂ L : E →L[ℝ] ℝ}
    (hx : x = t • y + (1-t) • z)
    (h₁ : HasFDerivAt v₁ L₁ y) (h₂ : HasFDerivAt v₂ L₂ z)
    (hφ : HasFDerivAt φ L x) (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ L = a • L₁ ∧ L = b • L₂ ∧
      t * a + (1-t) * b = 1 := by
  have hlin₁ : L₁.toLinearMap ≠ 0 := by
    intro h
    apply hL₁
    ext u
    exact congrArg (fun T : E →ₗ[ℝ] ℝ => T u) h
  have hlin₂ : L₂.toLinearMap ≠ 0 := by
    intro h
    apply hL₂
    ext u
    exact congrArg (fun T : E →ₗ[ℝ] ℝ => T u) h
  obtain ⟨a,b,ha,hb,hA,hB,hnorm⟩ := touching_linear_positive_proportional ht ht1
    L.toLinearMap L₁.toLinearMap L₂.toLinearMap hlin₁ hlin₂
      (touching_first_variation hx h₁ h₂ hφ hv₁ hv₂ htouch)
  refine ⟨a,b,ha,hb,?_,?_,hnorm⟩
  · ext u
    exact congrArg (fun T : E →ₗ[ℝ] ℝ => T u) hA
  · ext u
    exact congrArg (fun T : E →ₗ[ℝ] ℝ => T u) hB

end BMCompactAnalytic

#print axioms BMCompactAnalytic.min_le_derivative_of_local_min_comparison
#print axioms BMCompactAnalytic.touching_first_variation
#print axioms BMCompactAnalytic.touching_fderiv_positive_proportional
