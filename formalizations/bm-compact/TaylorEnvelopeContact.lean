import TaylorViscosity
import TouchingPLaplace

/-! Punctual second-order Taylor version of manuscript Lemmas 5.2 and 5.3,
proved in one shot by passing to the `C^∞` quadratic lower models
`quadModel (u₁ y) g₁ (A₁ - δ • id) y ≤ u₁` and `quadModel (v₁ z) g₂ (A₂ - δ • id) z ≤ v₁`,
applying the already-proved `C²` touching comparison, and letting `δ ↓ 0`. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric InnerProductSpace
open scoped Topology ContDiff BigOperators
namespace BMCompactPDE

section TaylorEnvelope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- First-order alignment from `min(⟪g₁, h⟫, ⟪g₂, k⟫) ≤ t⟪gφ, h⟫ + (1-t)⟪gφ, k⟫`. -/
theorem first_order_min_alignment {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {g₁ g₂ gφ : E} (hgφ : gφ ≠ 0)
    (hineq : ∀ h k : E, min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤
      t * inner ℝ gφ h + (1 - t) * inner ℝ gφ k) :
    let d := ‖gφ‖
    let ν := (-d⁻¹) • gφ
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      g₁ = (-a) • ν ∧ g₂ = (-b) • ν ∧ gφ = (-d) • ν ∧
      1 / d = t / a + (1 - t) / b := by
  intro d ν
  have hd : 0 < d := norm_pos_iff.mpr hgφ
  have hν_eq : gφ = (-d) • ν := by
    dsimp only [ν]
    rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ hd.ne', one_smul]
  have halign (g : E) (c0 : ℝ) (hc0 : 0 < c0)
      (h1 : ∀ h : E, min (inner ℝ g h) 0 ≤ c0 * inner ℝ gφ h) :
      ∃ c : ℝ, c0 ≤ c ∧ g = c • gφ := by
    have hker : ∀ h : E, inner ℝ g h = 0 → inner ℝ gφ h = 0 := by
      intro h hh
      have hp := h1 h; rw [hh, min_self] at hp
      have hm := h1 (-h); rw [inner_neg_right, hh, neg_zero, min_self, inner_neg_right] at hm
      nlinarith
    have hg_ne : g ≠ 0 := by
      intro hg0; subst hg0
      have h := h1 (-gφ)
      rw [inner_zero_left, min_self, inner_neg_right, real_inner_self_eq_norm_sq] at h
      have hsq : 0 < ‖gφ‖ ^ 2 := sq_pos_of_pos hd
      nlinarith
    let α : ℝ := inner ℝ g gφ / ‖g‖ ^ 2
    have hgn : 0 < ‖g‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg_ne)
    let h0 : E := gφ - α • g
    have hh0 : inner ℝ g h0 = 0 := by
      dsimp only [h0, α]
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hgn.ne']; ring
    have hφh0 : inner ℝ gφ h0 = 0 := hker h0 hh0
    have hh0_sq : ‖h0‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      calc inner ℝ h0 h0 = inner ℝ gφ h0 - α * inner ℝ g h0 := by
            dsimp only [h0]; rw [inner_sub_left, real_inner_smul_left]
        _ = 0 := by rw [hφh0, hh0]; ring
    have hgφ_eq : gφ = α • g := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hh0_sq))
    have hα_ne : α ≠ 0 := by
      intro h0'; rw [h0', zero_smul] at hgφ_eq; exact hgφ hgφ_eq
    have hg_eq : g = α⁻¹ • gφ := by rw [hgφ_eq, smul_smul, inv_mul_cancel₀ hα_ne, one_smul]
    have htest := h1 (-gφ)
    simp only [hg_eq, real_inner_smul_left, inner_neg_right, real_inner_self_eq_norm_sq] at htest
    have hsq : 0 < ‖gφ‖ ^ 2 := sq_pos_of_pos hd
    have hαinv_ge : c0 ≤ α⁻¹ := by
      rcases min_cases (-(α⁻¹ * ‖gφ‖ ^ 2)) 0 with ⟨heq, _⟩ | ⟨heq, _⟩ <;> nlinarith
    exact ⟨α⁻¹, hαinv_ge, hg_eq⟩
  obtain ⟨c₁, hc₁, hg₁_eq⟩ := halign g₁ t ht (fun h => by simpa using hineq h 0)
  obtain ⟨c₂, hc₂, hg₂_eq⟩ := halign g₂ (1 - t) (sub_pos.mpr ht1) (fun k => by simpa [min_comm] using hineq 0 k)
  have hc₁_pos : 0 < c₁ := lt_of_lt_of_le ht hc₁
  have hc₂_pos : 0 < c₂ := lt_of_lt_of_le (sub_pos.mpr ht1) hc₂
  have hsum_ge : 1 ≤ t / c₁ + (1 - t) / c₂ := by
    have h := hineq (c₁⁻¹ • gφ) (c₂⁻¹ • gφ)
    simp only [hg₁_eq, hg₂_eq, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h
    have h1 : c₁⁻¹ * (c₁ * ‖gφ‖ ^ 2) = ‖gφ‖ ^ 2 := by field_simp [hc₁_pos.ne']
    have h2 : c₂⁻¹ * (c₂ * ‖gφ‖ ^ 2) = ‖gφ‖ ^ 2 := by field_simp [hc₂_pos.ne']
    rw [h1, h2, min_self] at h
    have hsq : 0 < ‖gφ‖ ^ 2 := sq_pos_of_pos hd
    have h4 : 1 ≤ t * c₁⁻¹ + (1 - t) * c₂⁻¹ := by nlinarith
    simpa [div_eq_mul_inv] using h4
  have hsum_le : t / c₁ + (1 - t) / c₂ ≤ 1 := by
    have h := hineq (-(c₁⁻¹ • gφ)) (-(c₂⁻¹ • gφ))
    simp only [hg₁_eq, hg₂_eq, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h
    have h1 : -(c₁⁻¹ * (c₁ * ‖gφ‖ ^ 2)) = -(‖gφ‖ ^ 2) := by field_simp [hc₁_pos.ne']
    have h2 : -(c₂⁻¹ * (c₂ * ‖gφ‖ ^ 2)) = -(‖gφ‖ ^ 2) := by field_simp [hc₂_pos.ne']
    rw [h1, h2, min_self] at h
    have hsq : 0 < ‖gφ‖ ^ 2 := sq_pos_of_pos hd
    have h4 : t * c₁⁻¹ + (1 - t) * c₂⁻¹ ≤ 1 := by nlinarith
    simpa [div_eq_mul_inv] using h4
  have hsum_eq : t / c₁ + (1 - t) / c₂ = 1 := le_antisymm hsum_le hsum_ge
  let a : ℝ := c₁ * d
  let b : ℝ := c₂ * d
  refine ⟨a, b, mul_pos hc₁_pos hd, mul_pos hc₂_pos hd, ?_, ?_, hν_eq, ?_⟩
  · rw [hg₁_eq, hν_eq, smul_smul]; dsimp only [a]; congr 1; ring
  · rw [hg₂_eq, hν_eq, smul_smul]; dsimp only [b]; congr 1; ring
  · dsimp only [a, b]
    calc 1 / d = (t / c₁ + (1 - t) / c₂) / d := by rw [hsum_eq]
      _ = t / (c₁ * d) + (1 - t) / (c₂ * d) := by field_simp [hc₁_pos.ne', hc₂_pos.ne', hd.ne']

/-- Punctual second-order Taylor version of Lemmas 5.2 and 5.3. -/
theorem taylor_envelope_normalizedPLaplacian_le
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u₁ v₁ φ : E → ℝ} {y z x : E} (hxyz : x = t • y + (1 - t) • z)
    {g₁ g₂ : E} {A₁ A₂ : E →L[ℝ] E}
    (htu : HasSecondOrderTaylorAt u₁ g₁ A₁ y)
    (htv : HasSecondOrderTaylorAt v₁ g₂ A₂ z)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hφ : ContDiffAt ℝ 2 φ x) (hgφ : gradient φ x ≠ 0)
    (hu_eq : u₁ y = φ x) (hv_eq : v₁ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y, z), min (u₁ q.1) (v₁ q.2) ≤ φ (t • q.1 + (1 - t) • q.2)) :
    let d := ‖gradient φ x‖
    let a := ‖g₁‖
    let b := ‖g₂‖
    t * (d / a) ^ 3 * matrixNormalizedPLaplacian p g₁ A₁ +
      (1 - t) * (d / b) ^ 3 * matrixNormalizedPLaplacian p g₂ A₂ ≤
      BMCompactAnalytic.normalizedPLaplacian p φ x := by
  intro d a b
  have hd : 0 < d := norm_pos_iff.mpr hgφ
  have ha : 0 < a := norm_pos_iff.mpr hg₁
  have hb : 0 < b := norm_pos_iff.mpr hg₂
  have hfor (δ : ℝ) (hδ : 0 < δ) :
      t * (d / a) ^ 3 * matrixNormalizedPLaplacian p g₁ (A₁ + (-δ) • ContinuousLinearMap.id ℝ E) +
        (1 - t) * (d / b) ^ 3 * matrixNormalizedPLaplacian p g₂ (A₂ + (-δ) • ContinuousLinearMap.id ℝ E) ≤
        BMCompactAnalytic.normalizedPLaplacian p φ x := by
    let B₁ : E →L[ℝ] E := A₁ + (-δ) • ContinuousLinearMap.id ℝ E
    let B₂ : E →L[ℝ] E := A₂ + (-δ) • ContinuousLinearMap.id ℝ E
    have hB₁s : ∀ u w, inner ℝ (B₁ u) w = inner ℝ u (B₁ w) := fun u w => by
      simp only [B₁, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, htu.1 u w]
    have hB₂s : ∀ u w, inner ℝ (B₂ u) w = inner ℝ u (B₂ w) := fun u w => by
      simp only [B₂, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, htv.1 u w]
    let q₁ : E → ℝ := quadModel (u₁ y) g₁ B₁ y
    let q₂ : E → ℝ := quadModel (v₁ z) g₂ B₂ z
    have hq₁2 : ContDiffAt ℝ 2 q₁ y := ((contDiff_quadModel (u₁ y) g₁ B₁ y).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hq₂2 : ContDiffAt ℝ 2 q₂ z := ((contDiff_quadModel (v₁ z) g₂ B₂ z).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hq₁_le : ∀ᶠ y' in 𝓝 y, q₁ y' ≤ u₁ y' := by
      have hlo := htu.2; rw [Asymptotics.isLittleO_iff] at hlo
      filter_upwards [hlo (half_pos hδ)] with y' hy'
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)] at hy'
      have h1 := (abs_le.mp hy').1
      dsimp only [q₁, quadModel, B₁]
      simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      linarith
    have hq₂_le : ∀ᶠ z' in 𝓝 z, q₂ z' ≤ v₁ z' := by
      have hlo := htv.2; rw [Asymptotics.isLittleO_iff] at hlo
      filter_upwards [hlo (half_pos hδ)] with z' hz'
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)] at hz'
      have h1 := (abs_le.mp hz').1
      dsimp only [q₂, quadModel, B₂]
      simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      linarith
    have hq_touch : ∀ᶠ q : E × E in 𝓝 (y, z),
        min (q₁ q.1) (q₂ q.2) ≤ φ (t • q.1 + (1 - t) • q.2) := by
      rw [nhds_prod_eq] at htouch ⊢
      filter_upwards [htouch, hq₁_le.prod_inl (𝓝 z), hq₂_le.prod_inr (𝓝 y)] with q hq h1 h2
      exact (min_le_min h1 h2).trans hq
    have hgq₁ : gradient q₁ y = g₁ := gradient_quadModel_self (u₁ y) g₁ hB₁s y
    have hgq₂ : gradient q₂ z = g₂ := gradient_quadModel_self (v₁ z) g₂ hB₂s z
    have hL₁ : fderiv ℝ q₁ y ≠ 0 := by
      intro h0; apply hg₁; rw [← hgq₁]; unfold gradient; rw [h0]; simp
    have hL₂ : fderiv ℝ q₂ z ≠ 0 := by
      intro h0; apply hg₂; rw [← hgq₂]; unfold gradient; rw [h0]; simp
    obtain ⟨α, β, hα, hβ, hf₁, hf₂, _, hH⟩ :=
      BMCompactAnalytic.local_touching_hessian_cubic_weights ht ht1 hxyz hq₁2 hq₂2 hφ
        hL₁ hL₂ (by simp [q₁, quadModel, hu_eq]) (by simp [q₂, quadModel, hv_eq]) hq_touch
    have hgrad_α : gradient φ x = α • g₁ := by
      rw [← hgq₁]; unfold gradient; rw [hf₁, map_smul]
    have hgrad_β : gradient φ x = β • g₂ := by
      rw [← hgq₂]; unfold gradient; rw [hf₂, map_smul]
    have hα_eq : α = d / a := by
      have hnorm := congrArg (fun w : E => ‖w‖) hgrad_α
      rw [norm_smul, Real.norm_of_nonneg hα.le] at hnorm
      exact eq_div_of_mul_eq ha.ne' hnorm.symm
    have hβ_eq : β = d / b := by
      have hnorm := congrArg (fun w : E => ‖w‖) hgrad_β
      rw [norm_smul, Real.norm_of_nonneg hβ.le] at hnorm
      exact eq_div_of_mul_eq hb.ne' hnorm.symm
    let ν : E := (-d⁻¹) • gradient φ x
    have hν_norm : ‖ν‖ = 1 := by
      dsimp only [ν]
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']
    have hgφ_ν : gradient φ x = (-d) • ν := by
      dsimp only [ν]; rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ hd.ne', one_smul]
    have hgq₁_ν : gradient q₁ y = (-a) • ν := by
      rw [hgq₁, show g₁ = α⁻¹ • gradient φ x by rw [hgrad_α, smul_smul, inv_mul_cancel₀ hα.ne', one_smul],
        hgφ_ν, smul_smul, hα_eq]
      congr 1; field_simp [hd.ne', ha.ne']
    have hgq₂_ν : gradient q₂ z = (-b) • ν := by
      rw [hgq₂, show g₂ = β⁻¹ • gradient φ x by rw [hgrad_β, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul],
        hgφ_ν, smul_smul, hβ_eq]
      congr 1; field_simp [hd.ne', hb.ne']
    have hcomp := BMCompactAnalytic.aligned_normalizedPLaplacian_comparison hp ha hb hd hν_norm
      hgq₁_ν hgq₂_ν hgφ_ν (fun e => show
        (t * (d / a) ^ 3) * ((BMCompactAnalytic.actualHessian q₁ y) e) e +
        ((1 - t) * (d / b) ^ 3) * ((BMCompactAnalytic.actualHessian q₂ z) e) e ≤
        ((BMCompactAnalytic.actualHessian φ x) e) e by
        rw [← hα_eq, ← hβ_eq]
        exact hH e)
    rw [normalizedPLaplacian_quadModel p (u₁ y) g₁ hB₁s y,
      normalizedPLaplacian_quadModel p (v₁ z) g₂ hB₂s z] at hcomp
    exact hcomp
  have hlim : Tendsto (fun δ : ℝ =>
      t * (d / a) ^ 3 * (matrixNormalizedPLaplacian p g₁ A₁ +
        (-δ) * matrixNormalizedPLaplacian p g₁ (ContinuousLinearMap.id ℝ E)) +
      (1 - t) * (d / b) ^ 3 * (matrixNormalizedPLaplacian p g₂ A₂ +
        (-δ) * matrixNormalizedPLaplacian p g₂ (ContinuousLinearMap.id ℝ E)))
      (𝓝[>] 0) (𝓝 (t * (d / a) ^ 3 * matrixNormalizedPLaplacian p g₁ A₁ +
        (1 - t) * (d / b) ^ 3 * matrixNormalizedPLaplacian p g₂ A₂)) := by
    have h1 : Tendsto (fun δ : ℝ =>
        t * (d / a) ^ 3 * (matrixNormalizedPLaplacian p g₁ A₁ +
          (-δ) * matrixNormalizedPLaplacian p g₁ (ContinuousLinearMap.id ℝ E)) +
        (1 - t) * (d / b) ^ 3 * (matrixNormalizedPLaplacian p g₂ A₂ +
          (-δ) * matrixNormalizedPLaplacian p g₂ (ContinuousLinearMap.id ℝ E)))
        (𝓝 0) (𝓝 (t * (d / a) ^ 3 * (matrixNormalizedPLaplacian p g₁ A₁ +
          (-0) * matrixNormalizedPLaplacian p g₁ (ContinuousLinearMap.id ℝ E)) +
        (1 - t) * (d / b) ^ 3 * (matrixNormalizedPLaplacian p g₂ A₂ +
          (-0) * matrixNormalizedPLaplacian p g₂ (ContinuousLinearMap.id ℝ E)))) :=
      ((tendsto_const_nhds.add (tendsto_id.neg.mul tendsto_const_nhds)).const_mul _).add
        ((tendsto_const_nhds.add (tendsto_id.neg.mul tendsto_const_nhds)).const_mul _)
    simpa using h1.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have h := hfor δ hδ
  rw [matrixNormalizedPLaplacian_add, matrixNormalizedPLaplacian_smul,
    matrixNormalizedPLaplacian_add, matrixNormalizedPLaplacian_smul] at h
  exact h

end TaylorEnvelope
end BMCompactPDE
#print axioms BMCompactPDE.first_order_min_alignment
#print axioms BMCompactPDE.taylor_envelope_normalizedPLaplacian_le
