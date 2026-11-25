import EnvelopePerturbation
import TaylorEnvelopeContact
import SupInfConv
import SupConvolutionProperties
import UpstreamSelectedDirichlet

/-!
General nonlinear sup-min envelope viscosity theorem (Lemma 7.2) for all
`1 < p < ∞` and all dimensions `n ≥ 2`, without any `C¹` or `C²` PDE
regularity assumption on `u` or `v`.

Proof strategy:
1. For a touching test `φ` at `x₀` with `W x₀ = min (u y₀) (v z₀) < M₀`:
   - If `u y₀ < v z₀` (or symmetrically `v z₀ < u y₀`), then `u` (or `v`) is
     touched directly from above by `y ↦ φ (t • y + (1 - t) • z₀)`, yielding
     `0 ≤ normalizedPLaplacian p φ x₀` by scaling.
   - If `u y₀ = v z₀ = W x₀ < M₀`, assume for contradiction
     `normalizedPLaplacian p φ x₀ = -s₀ < 0`.
2. Add a small quadratic `γ ‖x - x₀‖²` to `φ` so `φ_γ` still has
   `normalizedPLaplacian p φ_γ < -s₀/2` near `x₀` and strictly dominates
   `W` away from `x₀`.
3. Take sup-convolutions `u^ε`, `v^ε` on a large compact ball `B_R` containing
   all superlevel optimizing pairs; for small `ε > 0`, `min(u^ε y, v^ε z) - φ_γ(t•y + (1-t)•z)`
   attains a maximum at an interior pair `(y_ε, z_ε)` with `x_ε := t•y_ε + (1-t)•z_ε`
   close to `x₀`.
4. Fix `σ > 0` small (independent of `ε`) and perturb to a strict local maximum
   at `(y_ε, z_ε)` via `u₁(y) = u^ε(y) - σ‖y - y_ε‖²`, `v₁(z) = v^ε(z) - σ‖z - z_ε‖²`,
   `φ̃(x) = φ_γ(x) + σ‖x - x_ε‖²`.
5. Apply `envelope_jensen_exists_good_maximizer` with `δ → 0` and Alexandrov's
   theorem to obtain a pair `(y_δ, z_δ) → (y_ε, z_ε)` where `u^ε, v^ε` have
   second-order Taylor expansions with uniform Hessian bounds `‖A₁'‖, ‖A₂'‖ ≤ K`.
6. Apply `taylor_envelope_normalizedPLaplacian_le`, the explicit Lipschitz
   estimate for `g ↦ matrixNormalizedPLaplacian p g A`, and
   `HasSecondOrderTaylorAt.matrixNormalizedPLaplacian_nonneg` to contradict
   `normalizedPLaplacian p φ̃ x_δ < -s₀/4`.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Metric MeasureTheory InnerProductSpace BMCompactEnvelope BMCompactAnalytic
open scoped Topology ContDiff NNReal BigOperators
namespace BMCompactPDE

section Helpers
variable {n : ℕ}

/-- Explicit Lipschitz bound for `g ↦ matrixNormalizedPLaplacian p g A` on the
exterior of `ball 0 r_lo` for operators `‖A‖ ≤ K`. -/
theorem abs_matrixNormalizedPLaplacian_sub_le {p r_lo K : ℝ}
    (hr : 0 < r_lo) (hK : 0 ≤ K) {g₁ g₂ : Space n}
    (hg₁ : r_lo ≤ ‖g₁‖) (hg₂ : r_lo ≤ ‖g₂‖)
    {A : Space n →L[ℝ] Space n} (hA : ‖A‖ ≤ K) :
    |matrixNormalizedPLaplacian p g₁ A - matrixNormalizedPLaplacian p g₂ A| ≤
      (4 * |p - 2| * K / r_lo) * ‖g₁ - g₂‖ := by
  have hg₁_pos : 0 < ‖g₁‖ := lt_of_lt_of_le hr hg₁
  have hg₂_pos : 0 < ‖g₂‖ := lt_of_lt_of_le hr hg₂
  let e₁ : Space n := ‖g₁‖⁻¹ • g₁
  let e₂ : Space n := ‖g₂‖⁻¹ • g₂
  have he₁ : ‖e₁‖ = 1 := by
    dsimp only [e₁]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hg₁_pos.le), inv_mul_cancel₀ hg₁_pos.ne']
  have he₂ : ‖e₂‖ = 1 := by
    dsimp only [e₂]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hg₂_pos.le), inv_mul_cancel₀ hg₂_pos.ne']
  have hdiff_e : ‖e₁ - e₂‖ ≤ 2 * ‖g₁ - g₂‖ / r_lo := by
    have hsplit : e₁ - e₂ = ‖g₁‖⁻¹ • (g₁ - g₂) + (‖g₁‖⁻¹ - ‖g₂‖⁻¹) • g₂ := by
      dsimp only [e₁, e₂]; module
    rw [hsplit]
    have h1 : ‖‖g₁‖⁻¹ • (g₁ - g₂)‖ ≤ ‖g₁ - g₂‖ / r_lo := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hg₁_pos.le), inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr hg₁
    have h2 : ‖(‖g₁‖⁻¹ - ‖g₂‖⁻¹) • g₂‖ ≤ ‖g₁ - g₂‖ / r_lo := by
      rw [norm_smul, Real.norm_eq_abs]
      have hinv : |‖g₁‖⁻¹ - ‖g₂‖⁻¹| * ‖g₂‖ = |‖g₂‖ - ‖g₁‖| / ‖g₁‖ := by
        have : ‖g₁‖⁻¹ - ‖g₂‖⁻¹ = (‖g₂‖ - ‖g₁‖) / (‖g₁‖ * ‖g₂‖) := by
          field_simp [hg₁_pos.ne', hg₂_pos.ne']
        rw [this, abs_div, abs_mul, abs_of_pos hg₁_pos, abs_of_pos hg₂_pos]
        field_simp [hg₁_pos.ne', hg₂_pos.ne']
      rw [hinv]
      calc |‖g₂‖ - ‖g₁‖| / ‖g₁‖
          ≤ ‖g₂ - g₁‖ / ‖g₁‖ := div_le_div_of_nonneg_right (abs_norm_sub_norm_le g₂ g₁) hg₁_pos.le
        _ = ‖g₁ - g₂‖ / ‖g₁‖ := by rw [norm_sub_rev]
        _ ≤ ‖g₁ - g₂‖ / r_lo := div_le_div_of_nonneg_left (norm_nonneg _) hr hg₁
    calc ‖‖g₁‖⁻¹ • (g₁ - g₂) + (‖g₁‖⁻¹ - ‖g₂‖⁻¹) • g₂‖
        ≤ ‖‖g₁‖⁻¹ • (g₁ - g₂)‖ + ‖(‖g₁‖⁻¹ - ‖g₂‖⁻¹) • g₂‖ := norm_add_le _ _
      _ ≤ ‖g₁ - g₂‖ / r_lo + ‖g₁ - g₂‖ / r_lo := add_le_add h1 h2
      _ = 2 * ‖g₁ - g₂‖ / r_lo := by ring
  have hunit (g : Space n) (hg : 0 < ‖g‖) :
      (‖g‖ ^ 2)⁻¹ * inner ℝ (A g) g = inner ℝ (A (‖g‖⁻¹ • g)) (‖g‖⁻¹ • g) := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    field_simp [hg.ne']
  have hsub_eq : matrixNormalizedPLaplacian p g₁ A - matrixNormalizedPLaplacian p g₂ A =
      (p - 2) * (inner ℝ (A e₁) e₁ - inner ℝ (A e₂) e₂) := by
    unfold matrixNormalizedPLaplacian
    rw [show (p - 2) * (‖g₁‖ ^ 2)⁻¹ * inner ℝ (A g₁) g₁ =
          (p - 2) * ((‖g₁‖ ^ 2)⁻¹ * inner ℝ (A g₁) g₁) by ring,
      show (p - 2) * (‖g₂‖ ^ 2)⁻¹ * inner ℝ (A g₂) g₂ =
          (p - 2) * ((‖g₂‖ ^ 2)⁻¹ * inner ℝ (A g₂) g₂) by ring,
      hunit g₁ hg₁_pos, hunit g₂ hg₂_pos]
    dsimp only [e₁, e₂]; ring
  rw [hsub_eq, abs_mul]
  have hquad : |inner ℝ (A e₁) e₁ - inner ℝ (A e₂) e₂| ≤ 2 * K * ‖e₁ - e₂‖ := by
    have hdecomp : inner ℝ (A e₁) e₁ - inner ℝ (A e₂) e₂ =
        inner ℝ (A (e₁ - e₂)) e₁ + inner ℝ (A e₂) (e₁ - e₂) := by
      rw [map_sub, inner_sub_left, inner_sub_right]; ring
    rw [hdecomp]
    have h1 : |inner ℝ (A (e₁ - e₂)) e₁| ≤ K * ‖e₁ - e₂‖ := by
      calc |inner ℝ (A (e₁ - e₂)) e₁|
          ≤ ‖A (e₁ - e₂)‖ * ‖e₁‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖e₁ - e₂‖) * 1 := by rw [he₁]; gcongr; exact A.le_opNorm _
        _ ≤ K * ‖e₁ - e₂‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    have h2 : |inner ℝ (A e₂) (e₁ - e₂)| ≤ K * ‖e₁ - e₂‖ := by
      calc |inner ℝ (A e₂) (e₁ - e₂)|
          ≤ ‖A e₂‖ * ‖e₁ - e₂‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * 1) * ‖e₁ - e₂‖ := by rw [← he₂]; gcongr; exact A.le_opNorm _
        _ ≤ K * ‖e₁ - e₂‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    calc |inner ℝ (A (e₁ - e₂)) e₁ + inner ℝ (A e₂) (e₁ - e₂)|
        ≤ |inner ℝ (A (e₁ - e₂)) e₁| + |inner ℝ (A e₂) (e₁ - e₂)| := abs_add_le _ _
      _ ≤ K * ‖e₁ - e₂‖ + K * ‖e₁ - e₂‖ := add_le_add h1 h2
      _ = 2 * K * ‖e₁ - e₂‖ := by ring
  calc |p - 2| * |inner ℝ (A e₁) e₁ - inner ℝ (A e₂) e₂|
      ≤ |p - 2| * (2 * K * ‖e₁ - e₂‖) := mul_le_mul_of_nonneg_left hquad (abs_nonneg _)
    _ ≤ |p - 2| * (2 * K * (2 * ‖g₁ - g₂‖ / r_lo)) := by gcongr
    _ = (4 * |p - 2| * K / r_lo) * ‖g₁ - g₂‖ := by ring

/-- Scaling of `normalizedPLaplacian` under affine reparametrization `y ↦ c • y + a`
with `c > 0`. -/
theorem normalizedPLaplacian_comp_smul_add {p c : ℝ} (hc : 0 < c) (a y₀ : Space n)
    {φ : Space n → ℝ} (hφ : ContDiffAt ℝ 2 φ (c • y₀ + a)) :
    gradient (fun y => φ (c • y + a)) y₀ = c • gradient φ (c • y₀ + a) ∧
    normalizedPLaplacian p (fun y => φ (c • y + a)) y₀ =
      c ^ 2 * normalizedPLaplacian p φ (c • y₀ + a) := by
  let ψ : Space n → ℝ := fun y => φ (c • y + a)
  let x₀ : Space n := c • y₀ + a
  have haff : ∀ y, HasFDerivAt (fun z : Space n => c • z + a) (c • ContinuousLinearMap.id ℝ (Space n)) y := by
    intro y
    simpa using ((hasFDerivAt_id y).const_smul c).add_const a
  have hgrad_all : ∀ᶠ y in 𝓝 y₀,
      fderiv ℝ ψ y = c • fderiv ℝ φ (c • y + a) := by
    have hcont : Continuous (fun y : Space n => c • y + a) :=
      (continuous_id.const_smul c).add continuous_const
    have hd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ φ x :=
      hφ.eventually (by norm_num) |>.mono fun x hx => hx.differentiableAt (by norm_num)
    filter_upwards [hcont.continuousAt.eventually hd] with y hy
    have hcomp : HasFDerivAt ψ
        ((fderiv ℝ φ (c • y + a)).comp (c • ContinuousLinearMap.id ℝ (Space n))) y :=
      hy.hasFDerivAt.comp y (haff y)
    rw [hcomp.fderiv]
    ext v; simp
  have hgrad0 : gradient ψ y₀ = c • gradient φ x₀ := by
    have h0 := hgrad_all.self_of_nhds
    unfold gradient
    rw [h0, map_smul]
  have hhess0 : actualHessian ψ y₀ = c ^ 2 • actualHessian φ x₀ := by
    have h1 : fderiv ℝ (fderiv ℝ ψ) y₀ = fderiv ℝ (fun y => c • fderiv ℝ φ (c • y + a)) y₀ :=
      Filter.EventuallyEq.fderiv_eq hgrad_all
    have h2 : HasFDerivAt (fun y => fderiv ℝ φ (c • y + a))
        ((fderiv ℝ (fderiv ℝ φ) x₀).comp (c • ContinuousLinearMap.id ℝ (Space n))) y₀ := by
      have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) x₀ :=
        (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      exact hd2.hasFDerivAt.comp y₀ (haff y₀)
    have h3 : HasFDerivAt (fun y => c • fderiv ℝ φ (c • y + a))
        (c • ((fderiv ℝ (fderiv ℝ φ) x₀).comp (c • ContinuousLinearMap.id ℝ (Space n)))) y₀ :=
      h2.const_smul c
    unfold actualHessian
    rw [h1, h3.fderiv]
    ext u v
    simp [sq, mul_assoc]
  refine ⟨hgrad0, ?_⟩
  have hlap : actualLaplacian ψ y₀ = c ^ 2 * actualLaplacian φ x₀ := by
    rw [actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) ψ y₀,
      actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) φ x₀, hhess0]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  change normalizedPLaplacian p ψ y₀ = c ^ 2 * normalizedPLaplacian p φ x₀
  unfold normalizedPLaplacian
  rw [hlap, hgrad0, hhess0]
  simp only [smul_apply, map_smul, smul_eq_mul,
    norm_smul, Real.norm_of_nonneg hc.le, mul_pow, mul_inv]
  by_cases hg : gradient φ x₀ = 0
  · simp [hg]
  · have hgn : ‖gradient φ x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    field_simp [hc.ne', hgn]

/-- Adding `γ * ‖x - x₀‖²` to a `C²` function `φ` shifts `normalizedPLaplacian`
at `x₀` by `2 * γ * ((n : ℝ) + p - 2)` and preserves the gradient at `x₀`. -/
theorem normalizedPLaplacian_add_quad_self (p γ : ℝ) (x₀ : Space n)
    {φ : Space n → ℝ} (hφ : ContDiffAt ℝ 2 φ x₀) (hg : gradient φ x₀ ≠ 0) :
    gradient (fun x => φ x + γ * ‖x - x₀‖ ^ 2) x₀ = gradient φ x₀ ∧
    normalizedPLaplacian p (fun x => φ x + γ * ‖x - x₀‖ ^ 2) x₀ =
      normalizedPLaplacian p φ x₀ + 2 * γ * ((n : ℝ) + p - 2) := by
  let q : Space n → ℝ := fun x => γ * ‖x - x₀‖ ^ 2
  have hq_eq : q = quadModel 0 0 ((2 * γ) • ContinuousLinearMap.id ℝ (Space n)) x₀ := by
    funext x
    simp only [q, quadModel, zero_add, inner_zero_left, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hsym : ∀ u v : Space n,
      inner ℝ (((2 * γ) • ContinuousLinearMap.id ℝ (Space n)) u) v =
      inner ℝ u (((2 * γ) • ContinuousLinearMap.id ℝ (Space n)) v) := by
    intro u v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right]
  have hq_c2 : ContDiff ℝ 2 q := by
    rw [hq_eq]
    exact (contDiff_quadModel 0 0 ((2 * γ) • ContinuousLinearMap.id ℝ (Space n)) x₀).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hq_fderiv : ∀ x, fderiv ℝ q x = toDual ℝ (Space n) ((2 * γ) • (x - x₀)) := by
    intro x
    rw [hq_eq]
    have h := (hasFDerivAt_quadModel 0 0 hsym x₀ x).fderiv
    simpa using h
  have hq_grad0 : gradient q x₀ = 0 := by
    unfold gradient
    rw [hq_fderiv x₀, sub_self, smul_zero, map_zero, map_zero]
  have hgrad0 : gradient (fun x => φ x + q x) x₀ = gradient φ x₀ := by
    have h1 := (hφ.differentiableAt (by norm_num)).hasFDerivAt
    have h2 := (hq_c2.differentiable (by norm_num) x₀).hasFDerivAt
    have h12 : HasFDerivAt (fun x => φ x + q x) (fderiv ℝ φ x₀ + fderiv ℝ q x₀) x₀ := h1.add h2
    unfold gradient
    rw [h12.fderiv, hq_fderiv x₀, sub_self, smul_zero, map_zero, add_zero]
  have hhess_q : ∀ u v : Space n, actualHessian q x₀ u v = (2 * γ) * inner ℝ u v := by
    intro u v
    rw [hq_eq, actualHessian_quadModel 0 0 hsym x₀ u v]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left]
  have hhess_sum : actualHessian (fun x => φ x + q x) x₀ =
      actualHessian φ x₀ + actualHessian q x₀ := by
    have hfd_ev : ∀ᶠ x in 𝓝 x₀, fderiv ℝ (fun y => φ y + q y) x = fderiv ℝ φ x + fderiv ℝ q x := by
      filter_upwards [hφ.eventually (by norm_num)] with x hx
      exact ((hx.differentiableAt (by norm_num)).hasFDerivAt.add
        (hq_c2.differentiable (by norm_num) x).hasFDerivAt).fderiv
    have h1 : fderiv ℝ (fderiv ℝ (fun y => φ y + q y)) x₀ =
        fderiv ℝ (fun x => fderiv ℝ φ x + fderiv ℝ q x) x₀ := Filter.EventuallyEq.fderiv_eq hfd_ev
    have hdφ : DifferentiableAt ℝ (fderiv ℝ φ) x₀ :=
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hdq : DifferentiableAt ℝ (fderiv ℝ q) x₀ :=
      (hq_c2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x₀
    have h2 : HasFDerivAt (fun x => fderiv ℝ φ x + fderiv ℝ q x)
        (fderiv ℝ (fderiv ℝ φ) x₀ + fderiv ℝ (fderiv ℝ q) x₀) x₀ :=
      hdφ.hasFDerivAt.add hdq.hasFDerivAt
    unfold actualHessian
    rw [h1, h2.fderiv]
  refine ⟨hgrad0, ?_⟩
  have hlap : actualLaplacian (fun x => φ x + q x) x₀ = actualLaplacian φ x₀ + 2 * γ * (n : ℝ) := by
    rw [actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) (fun x => φ x + q x) x₀,
      actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) φ x₀, hhess_sum]
    have hbnorm (i : Fin n) : ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 :=
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i
    simp only [ContinuousLinearMap.add_apply, hhess_q, real_inner_self_eq_norm_sq,
      hbnorm, one_pow, mul_one,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  unfold normalizedPLaplacian
  rw [hgrad0, hlap, hhess_sum]
  simp only [ContinuousLinearMap.add_apply, hhess_q, real_inner_self_eq_norm_sq]
  have hgn : ‖gradient φ x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  field_simp [hgn]
  ring

/-- Continuity of `x ↦ normalizedPLaplacian p φ x` at a noncritical point `x₀`
of a `C²` function `φ` on an open set `U`. -/
theorem continuousAt_normalizedPLaplacian {p : ℝ} {U : Set (Space n)} (hU : IsOpen U)
    {φ : Space n → ℝ} (hφ : ContDiffOn ℝ 2 φ U) {x₀ : Space n} (hx₀ : x₀ ∈ U)
    (hg : gradient φ x₀ ≠ 0) :
    ContinuousAt (fun x => normalizedPLaplacian p φ x) x₀ := by
  have hφ_at : ContDiffAt ℝ 2 φ x₀ := hφ.contDiffAt (hU.mem_nhds hx₀)
  have hgrad_cont : ContinuousAt (gradient φ) x₀ := by
    have hfd : ContinuousAt (fderiv ℝ φ) x₀ :=
      (hφ_at.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact (toDual ℝ (Space n)).symm.continuous.continuousAt.comp hfd
  have hhess_cont : ContinuousAt (actualHessian φ) x₀ := by
    have hfd2 : ContinuousAt (fderiv ℝ (fderiv ℝ φ)) x₀ :=
      ((hφ_at.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact hfd2
  have hlap_cont : ContinuousAt (actualLaplacian φ) x₀ := by
    have heq : actualLaplacian φ = fun x =>
        ∑ i : Fin n, actualHessian φ x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      funext x
      exact actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) φ x
    rw [heq]
    refine tendsto_finset_sum _ fun i _ => ?_
    have h1 : ContinuousAt (fun x => actualHessian φ x (EuclideanSpace.basisFun (Fin n) ℝ i)) x₀ :=
      (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).continuous.continuousAt.comp hhess_cont
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).continuous.continuousAt.comp h1
  have hquad_cont : ContinuousAt (fun x => actualHessian φ x (gradient φ x) (gradient φ x)) x₀ := by
    have h1 : ContinuousAt (fun x => actualHessian φ x (gradient φ x)) x₀ :=
      isBoundedBilinearMap_apply.continuous.continuousAt.comp (hhess_cont.prodMk hgrad_cont)
    exact isBoundedBilinearMap_apply.continuous.continuousAt.comp (h1.prodMk hgrad_cont)
  have hnorm_ne : ‖gradient φ x₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  unfold normalizedPLaplacian
  refine hlap_cont.add ?_
  exact (continuousAt_const.mul ((hgrad_cont.norm.pow 2).inv₀ hnorm_ne)).mul hquad_cont

/-- Shifting a function with a second-order Taylor expansion by `-σ‖· - y₀‖² + ⟪p, ·⟫ + c`. -/
theorem HasSecondOrderTaylorAt.sub_quad_add_lin_const {u : Space n → ℝ} {g : Space n}
    {A : Space n →L[ℝ] Space n} {y : Space n}
    (ht : HasSecondOrderTaylorAt u g A y) (σ : ℝ) (y₀ p : Space n) (c : ℝ) :
    HasSecondOrderTaylorAt
      (fun y' => u y' - σ * ‖y' - y₀‖ ^ 2 + inner ℝ p y' + c)
      (g - (2 * σ) • (y - y₀) + p)
      (A - (2 * σ) • ContinuousLinearMap.id ℝ (Space n)) y := by
  refine ⟨fun u' v' => ?_, ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, ht.1 u' v']
  · refine ht.2.congr' (Eventually.of_forall fun y' => ?_) (Eventually.of_forall fun _ => rfl)
    have hnorm : ‖y' - y₀‖ ^ 2 - ‖y - y₀‖ ^ 2 =
        ‖y' - y‖ ^ 2 + 2 * inner ℝ (y - y₀) (y' - y) := by
      have hvec : y' - y₀ = (y' - y) + (y - y₀) := by abel
      conv_lhs => rw [hvec, norm_add_sq_real]
      rw [real_inner_comm (y' - y) (y - y₀)]; ring
    have hny : ‖y' - y₀‖ ^ 2 = ‖y - y₀‖ ^ 2 + ‖y' - y‖ ^ 2 + 2 * inner ℝ (y - y₀) (y' - y) := by
      linarith [hnorm]
    have h1 : inner ℝ (g - (2 * σ) • (y - y₀) + p) (y' - y) =
        inner ℝ g (y' - y) - 2 * σ * inner ℝ (y - y₀) (y' - y) + inner ℝ p y' - inner ℝ p y := by
      rw [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right p y' y]; ring
    have h2 : inner ℝ ((A - (2 * σ) • ContinuousLinearMap.id ℝ (Space n)) (y' - y)) (y' - y) =
        inner ℝ (A (y' - y)) (y' - y) - 2 * σ * ‖y' - y‖ ^ 2 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    dsimp only
    rw [h1, h2, hny]
    ring

end Helpers

section MainEnvelope
variable {n : ℕ}

/-- Core contradiction step for the nonlinear envelope: if `uε, vε` are
`(1/ε)`-semiconvex viscosity `p`-subsolutions on open neighborhoods of `yε, zε`,
`uε yε = vε zε`, and `(yε, zε)` maximizes `min(uε y, vε z) - φγ(t•y + (1-t)•z)`
locally while `normalizedPLaplacian p φγ (t•yε + (1-t)•zε) < -(5/8) * s₀ < 0`,
we obtain a contradiction via `envelope_jensen_exists_good_maximizer` and
Alexandrov's theorem. -/
private theorem envelope_semiconvex_contradiction (hn : 2 ≤ n) {p t ε s₀ : ℝ}
    (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1) (hε : 0 < ε) (hs₀ : 0 < s₀)
    {Lε : ℝ≥0} {uε vε φγ : Space n → ℝ}
    (hfuε_conv : ConvexOn ℝ univ (fun y => uε y + (1 / (2 * ε)) * ‖y‖ ^ 2))
    (hfuε_lip : LipschitzWith Lε (fun y => uε y + (1 / (2 * ε)) * ‖y‖ ^ 2))
    (hfvε_conv : ConvexOn ℝ univ (fun z => vε z + (1 / (2 * ε)) * ‖z‖ ^ 2))
    (hfvε_lip : LipschitzWith Lε (fun z => vε z + (1 / (2 * ε)) * ‖z‖ ^ 2))
    {Ωu Ωv U : Set (Space n)} (hΩu : IsOpen Ωu) (hΩv : IsOpen Ωv) (hU : IsOpen U)
    (huε_visc : IsViscosityPSubsolution p Ωu uε)
    (hvε_visc : IsViscosityPSubsolution p Ωv vε)
    (hφγ_U : ContDiffOn ℝ 2 φγ U)
    {yε zε : Space n} (hyε_Ωu : yε ∈ Ωu) (hzε_Ωv : zε ∈ Ωv)
    (hxε_U : t • yε + (1 - t) • zε ∈ U)
    (hgrad_xε : gradient φγ (t • yε + (1 - t) • zε) ≠ 0)
    (hlap_xε : normalizedPLaplacian p φγ (t • yε + (1 - t) • zε) < -(5 / 8 : ℝ) * s₀)
    (heq_val : uε yε = vε zε)
    {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hloc_max : ∀ y ∈ closedBall yε ρ₁, ∀ z ∈ closedBall zε ρ₁,
      min (uε y) (vε z) - φγ (t • y + (1 - t) • z) ≤
      min (uε yε) (vε zε) - φγ (t • yε + (1 - t) • zε)) :
    False := by
  classical
  have ht1_pos : 0 < 1 - t := sub_pos.mpr ht1
  have hnp_pos : (0 : ℝ) < (n : ℝ) + p - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let xε : Space n := t • yε + (1 - t) • zε
  -- Fix σ > 0 small (independent of ε!)
  let σ : ℝ := s₀ / (32 * ((n : ℝ) + p - 2) * (1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2))
  have hσ : 0 < σ := div_pos hs₀ (by positivity)
  have hσ_eq : 2 * σ * ((n : ℝ) + p - 2) * (1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) = s₀ / 16 := by
    dsimp only [σ]
    have hden : 32 * ((n : ℝ) + p - 2) * (1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) ≠ 0 := by positivity
    field_simp [hden]; ring
  let u₁ : Space n → ℝ := fun y => uε y - σ * ‖y - yε‖ ^ 2
  let v₁ : Space n → ℝ := fun z => vε z - σ * ‖z - zε‖ ^ 2
  let φt : Space n → ℝ := fun x => φγ x + σ * ‖x - xε‖ ^ 2
  have hφt_U : ContDiffOn ℝ 2 φt U :=
    hφγ_U.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffOn
  have hφγ_at : ContDiffAt ℝ 2 φγ xε := hφγ_U.contDiffAt (hU.mem_nhds hxε_U)
  obtain ⟨hgrad_φt0, hlap_φt0⟩ := normalizedPLaplacian_add_quad_self p σ xε hφγ_at hgrad_xε
  have hgrad_φt_ne0 : gradient φt xε ≠ 0 := by rw [hgrad_φt0]; exact hgrad_xε
  have h2σ_le : 2 * σ * ((n : ℝ) + p - 2) ≤ s₀ / 16 := by
    have h1 : (1 : ℝ) ≤ 1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2 := by
      linarith [sq_nonneg t⁻¹, sq_nonneg (1 - t)⁻¹]
    calc 2 * σ * ((n : ℝ) + p - 2)
        = 2 * σ * ((n : ℝ) + p - 2) * 1 := (mul_one _).symm
      _ ≤ 2 * σ * ((n : ℝ) + p - 2) * (1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s₀ / 16 := hσ_eq
  have hlap_φt0_lt : normalizedPLaplacian p φt xε < -(1 / 2 : ℝ) * s₀ := by
    rw [hlap_φt0]; linarith
  -- Choose radius ρ > 0 small enough that:
  -- closedBall yε ρ ⊆ Ωu, closedBall zε ρ ⊆ Ωv, closedBall xε (2*ρ) ⊆ U,
  -- gradient φt x ≠ 0 and ‖gradient φt x‖ ≥ d₀ / 2 and normalizedPLaplacian p φt x < -(3/8)*s₀
  -- on closedBall xε (2*ρ)
  let d₀ : ℝ := ‖gradient φt xε‖
  have hd₀ : 0 < d₀ := norm_pos_iff.mpr hgrad_φt_ne0
  have hφt_at : ContDiffAt ℝ 2 φt xε := hφt_U.contDiffAt (hU.mem_nhds hxε_U)
  have hgrad_φt_cont : ContinuousAt (gradient φt) xε :=
    (toDual ℝ (Space n)).symm.continuous.continuousAt.comp
      ((hφt_at.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hlap_φt_cont : ContinuousAt (fun x => normalizedPLaplacian p φt x) xε :=
    continuousAt_normalizedPLaplacian hU hφt_U hxε_U hgrad_φt_ne0
  have hev_x : ∀ᶠ x in 𝓝 xε,
      x ∈ U ∧ d₀ / 2 < ‖gradient φt x‖ ∧ normalizedPLaplacian p φt x < -(3 / 8 : ℝ) * s₀ := by
    filter_upwards [hU.mem_nhds hxε_U,
      hgrad_φt_cont.norm.eventually (eventually_gt_nhds (half_lt_self hd₀)),
      hlap_φt_cont.eventually (eventually_lt_nhds (by linarith : normalizedPLaplacian p φt xε < -(3 / 8 : ℝ) * s₀))]
      with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r_x, hr_x, hr_x_prop⟩ := Metric.eventually_nhds_iff.mp hev_x
  obtain ⟨r_u, hr_u, hr_u_prop⟩ := Metric.isOpen_iff.mp hΩu yε hyε_Ωu
  obtain ⟨r_v, hr_v, hr_v_prop⟩ := Metric.isOpen_iff.mp hΩv zε hzε_Ωv
  let ρ : ℝ := min (min ρ₁ (r_x / 4)) (min (r_u / 2) (r_v / 2))
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ (by positivity)) (lt_min (half_pos hr_u) (half_pos hr_v))
  have hsub_u : closedBall yε ρ ⊆ Ωu := fun y hy => hr_u_prop <| by
    rw [mem_ball]
    have := mem_closedBall.mp hy
    have hρu : ρ ≤ r_u / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hsub_v : closedBall zε ρ ⊆ Ωv := fun z hz => hr_v_prop <| by
    rw [mem_ball]
    have := mem_closedBall.mp hz
    have hρv : ρ ≤ r_v / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hsub_x (x : Space n) (hx : x ∈ closedBall xε (2 * ρ)) :
      x ∈ U ∧ d₀ / 2 < ‖gradient φt x‖ ∧ normalizedPLaplacian p φt x < -(3 / 8 : ℝ) * s₀ := by
    apply hr_x_prop
    have := mem_closedBall.mp hx
    have hρx : ρ ≤ r_x / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  -- Semiconvexity & Lipschitz of u₁ and v₁ with M := 1/ε + 2*σ
  let M : ℝ := 1 / ε + 2 * σ
  have hM : 0 < M := by positivity
  -- u₁ y + (M/2)‖y‖² = (uε y + (1/(2ε))‖y‖²) + σ * (2⟪yε, y⟫ - ‖yε‖²)
  have hu₁_id (y : Space n) :
      u₁ y + (M / 2) * ‖y‖ ^ 2 =
        (uε y + (1 / (2 * ε)) * ‖y‖ ^ 2) + (2 * σ) * inner ℝ yε y - σ * ‖yε‖ ^ 2 := by
    dsimp only [u₁, M]
    rw [norm_sub_sq_real, real_inner_comm y yε]; ring
  have hv₁_id (z : Space n) :
      v₁ z + (M / 2) * ‖z‖ ^ 2 =
        (vε z + (1 / (2 * ε)) * ‖z‖ ^ 2) + (2 * σ) * inner ℝ zε z - σ * ‖zε‖ ^ 2 := by
    dsimp only [v₁, M]
    rw [norm_sub_sq_real, real_inner_comm z zε]; ring
  have hf₁_conv : ConvexOn ℝ univ (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2) := by
    have heq : (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2) =
        fun y => ((uε y + (1 / (2 * ε)) * ‖y‖ ^ 2) + inner ℝ ((2 * σ) • yε) y) + (-(σ * ‖yε‖ ^ 2)) := by
      funext y; rw [hu₁_id, real_inner_smul_left]; ring
    rw [heq]
    have hlin : ConvexOn ℝ univ (fun y : Space n => inner ℝ ((2 * σ) • yε) y) :=
      (toDual ℝ (Space n) ((2 * σ) • yε)).toLinearMap.convexOn convex_univ
    exact (hfuε_conv.add hlin).add_const _
  have hf₂_conv : ConvexOn ℝ univ (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2) := by
    have heq : (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2) =
        fun z => ((vε z + (1 / (2 * ε)) * ‖z‖ ^ 2) + inner ℝ ((2 * σ) • zε) z) + (-(σ * ‖zε‖ ^ 2)) := by
      funext z; rw [hv₁_id, real_inner_smul_left]; ring
    rw [heq]
    have hlin : ConvexOn ℝ univ (fun z : Space n => inner ℝ ((2 * σ) • zε) z) :=
      (toDual ℝ (Space n) ((2 * σ) • zε)).toLinearMap.convexOn convex_univ
    exact (hfvε_conv.add hlin).add_const _
  let c₁ : ℝ≥0 := ⟨2 * σ * max ‖yε‖ ‖zε‖, by positivity⟩
  let L₁ : ℝ≥0 := Lε + c₁
  have hL₁ : (L₁ : ℝ) = (Lε : ℝ) + 2 * σ * max ‖yε‖ ‖zε‖ := by
    change ((Lε + c₁ : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_add]
    rfl
  have hf₁_lip : LipschitzWith L₁ (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, hu₁_id a, hu₁_id b]
    have hdiff : ((uε a + (1 / (2 * ε)) * ‖a‖ ^ 2) + 2 * σ * inner ℝ yε a - σ * ‖yε‖ ^ 2) -
        ((uε b + (1 / (2 * ε)) * ‖b‖ ^ 2) + 2 * σ * inner ℝ yε b - σ * ‖yε‖ ^ 2) =
        ((uε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (uε b + (1 / (2 * ε)) * ‖b‖ ^ 2)) +
        2 * σ * inner ℝ yε (a - b) := by
      rw [inner_sub_right]; ring
    rw [hdiff]
    have h1 := hfuε_lip.dist_le_mul a b
    rw [Real.dist_eq] at h1
    have h2 : |2 * σ * inner ℝ yε (a - b)| ≤ (2 * σ * max ‖yε‖ ‖zε‖) * dist a b := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ), dist_eq_norm]
      calc (2 * σ) * |inner ℝ yε (a - b)|
          ≤ (2 * σ) * (‖yε‖ * ‖a - b‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
        _ ≤ (2 * σ) * (max ‖yε‖ ‖zε‖ * ‖a - b‖) := by gcongr; exact le_max_left _ _
        _ = (2 * σ * max ‖yε‖ ‖zε‖) * ‖a - b‖ := by ring
    calc |((uε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (uε b + (1 / (2 * ε)) * ‖b‖ ^ 2)) +
          2 * σ * inner ℝ yε (a - b)|
        ≤ |(uε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (uε b + (1 / (2 * ε)) * ‖b‖ ^ 2)| +
          |2 * σ * inner ℝ yε (a - b)| := abs_add_le _ _
      _ ≤ (Lε : ℝ) * dist a b + (2 * σ * max ‖yε‖ ‖zε‖) * dist a b := add_le_add h1 h2
      _ = (L₁ : ℝ) * dist a b := by rw [hL₁]; ring
  have hf₂_lip : LipschitzWith L₁ (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, hv₁_id a, hv₁_id b]
    have hdiff : ((vε a + (1 / (2 * ε)) * ‖a‖ ^ 2) + 2 * σ * inner ℝ zε a - σ * ‖zε‖ ^ 2) -
        ((vε b + (1 / (2 * ε)) * ‖b‖ ^ 2) + 2 * σ * inner ℝ zε b - σ * ‖zε‖ ^ 2) =
        ((vε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (vε b + (1 / (2 * ε)) * ‖b‖ ^ 2)) +
        2 * σ * inner ℝ zε (a - b) := by
      rw [inner_sub_right]; ring
    rw [hdiff]
    have h1 := hfvε_lip.dist_le_mul a b
    rw [Real.dist_eq] at h1
    have h2 : |2 * σ * inner ℝ zε (a - b)| ≤ (2 * σ * max ‖yε‖ ‖zε‖) * dist a b := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ), dist_eq_norm]
      calc (2 * σ) * |inner ℝ zε (a - b)|
          ≤ (2 * σ) * (‖zε‖ * ‖a - b‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
        _ ≤ (2 * σ) * (max ‖yε‖ ‖zε‖ * ‖a - b‖) := by gcongr; exact le_max_right _ _
        _ = (2 * σ * max ‖yε‖ ‖zε‖) * ‖a - b‖ := by ring
    calc |((vε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (vε b + (1 / (2 * ε)) * ‖b‖ ^ 2)) +
          2 * σ * inner ℝ zε (a - b)|
        ≤ |(vε a + (1 / (2 * ε)) * ‖a‖ ^ 2) - (vε b + (1 / (2 * ε)) * ‖b‖ ^ 2)| +
          |2 * σ * inner ℝ zε (a - b)| := abs_add_le _ _
      _ ≤ (Lε : ℝ) * dist a b + (2 * σ * max ‖yε‖ ‖zε‖) * dist a b := add_le_add h1 h2
      _ = (L₁ : ℝ) * dist a b := by rw [hL₁]; ring
  -- Strict maximum of min(u₁ y, v₁ z) - φt(t•y + (1-t)•z) at (yε, zε) on closedBall yε ρ × closedBall zε ρ
  have hstrict : ∀ y ∈ closedBall yε ρ, ∀ z ∈ closedBall zε ρ, (y, z) ≠ (yε, zε) →
      min (u₁ y) (v₁ z) - φt (t • y + (1 - t) • z) <
      min (u₁ yε) (v₁ zε) - φt (t • yε + (1 - t) • zε) := by
    intro y hy z hz hne
    have hρ_le : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hloc := hloc_max y (closedBall_subset_closedBall hρ_le hy) z (closedBall_subset_closedBall hρ_le hz)
    have h0 : min (u₁ yε) (v₁ zε) - φt (t • yε + (1 - t) • zε) =
        min (uε yε) (vε zε) - φγ (t • yε + (1 - t) • zε) := by
      simp [u₁, v₁, φt, xε]
    rw [h0]
    by_cases hx : t • y + (1 - t) • z = xε
    · -- Then y ≠ yε AND z ≠ zε!
      have hy_ne : y ≠ yε := by
        intro hy_eq; subst hy_eq
        apply hne; congr 1
        have h1 : (1 - t) • (z - zε) = 0 := by
          have : t • y + (1 - t) • z - (t • y + (1 - t) • zε) = 0 := by rw [hx]; dsimp only [xε]; abel
          simpa [smul_sub] using this
        rcases smul_eq_zero.mp h1 with h0' | h0'
        · exact absurd h0' ht1_pos.ne'
        · exact sub_eq_zero.mp h0'
      have hz_ne : z ≠ zε := by
        intro hz_eq; subst hz_eq
        apply hne; congr 1
        have h1 : t • (y - yε) = 0 := by
          have : t • y + (1 - t) • z - (t • yε + (1 - t) • z) = 0 := by rw [hx]; dsimp only [xε]; abel
          simpa [smul_sub] using this
        rcases smul_eq_zero.mp h1 with h0' | h0'
        · exact absurd h0' ht.ne'
        · exact sub_eq_zero.mp h0'
      have h1 : u₁ y < uε y := by
        dsimp only [u₁]
        have : 0 < σ * ‖y - yε‖ ^ 2 := mul_pos hσ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hy_ne)))
        linarith
      have h2 : v₁ z < vε z := by
        dsimp only [v₁]
        have : 0 < σ * ‖z - zε‖ ^ 2 := mul_pos hσ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne)))
        linarith
      have hmin_lt : min (u₁ y) (v₁ z) < min (uε y) (vε z) := by
        rcases min_cases (uε y) (vε z) with ⟨h, _⟩ | ⟨h, _⟩ <;>
          simp only [h, min_lt_iff] <;> [exact Or.inl h1; exact Or.inr h2]
      have hφ_ge : φγ (t • y + (1 - t) • z) ≤ φt (t • y + (1 - t) • z) := by
        dsimp only [φt]; linarith [mul_nonneg hσ.le (sq_nonneg ‖t • y + (1 - t) • z - xε‖)]
      linarith
    · -- t•y + (1-t)•z ≠ xε, so φt > φγ strictly
      have hφ_lt : φγ (t • y + (1 - t) • z) < φt (t • y + (1 - t) • z) := by
        dsimp only [φt]
        have : 0 < σ * ‖t • y + (1 - t) • z - xε‖ ^ 2 :=
          mul_pos hσ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))
        linarith
      have hmin_le : min (u₁ y) (v₁ z) ≤ min (uε y) (vε z) := by
        apply min_le_min <;> dsimp only [u₁, v₁] <;>
          linarith [mul_nonneg hσ.le (sq_nonneg ‖y - yε‖), mul_nonneg hσ.le (sq_nonneg ‖z - zε‖)]
      linarith
  -- Alexandrov full-measure sets A₁, A₂ for f₁_ε, f₂_ε
  haveI : Nontrivial (Space n) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ 1, ?_⟩⟩
    intro h0
    have := congrArg (fun x : Space n => x.ofLp ⟨0, by omega⟩) h0
    simp at this
  let A₁ : Set (Space n) :=
    {y | DifferentiableAt ℝ (fun y' => uε y' + (1 / (2 * ε)) * ‖y'‖ ^ 2) y ∧
      ∃ A : Space n →L[ℝ] Space n,
        HasSecondOrderTaylorAt (fun y' => uε y' + (1 / (2 * ε)) * ‖y'‖ ^ 2)
          (gradient (fun y' => uε y' + (1 / (2 * ε)) * ‖y'‖ ^ 2) y) A y}
  let A₂ : Set (Space n) :=
    {z | DifferentiableAt ℝ (fun z' => vε z' + (1 / (2 * ε)) * ‖z'‖ ^ 2) z ∧
      ∃ A : Space n →L[ℝ] Space n,
        HasSecondOrderTaylorAt (fun z' => vε z' + (1 / (2 * ε)) * ‖z'‖ ^ 2)
          (gradient (fun z' => vε z' + (1 / (2 * ε)) * ‖z'‖ ^ 2) z) A z}
  have hA₁ : volume A₁ᶜ = 0 := by
    have hae := alexandrov_convex_lipschitz (volume : Measure (Space n)) hfuε_conv hfuε_lip
    rwa [ae_iff] at hae
  have hA₂ : volume A₂ᶜ = 0 := by
    have hae := alexandrov_convex_lipschitz (volume : Measure (Space n)) hfvε_conv hfvε_lip
    rwa [ae_iff] at hae
  -- Apply envelope_jensen_exists_good_maximizer!
  obtain ⟨ρ₀, C_upper, hρ₀, hC_upper, hgood⟩ := envelope_jensen_exists_good_maximizer hn ht ht1 hM
    hf₁_conv hf₁_lip hf₂_conv hf₂_lip hρ hU hφt_U
    (fun x hx => (hsub_x x hx).1)
    (fun x hx => norm_pos_iff.mp (lt_trans (half_pos hd₀) (hsub_x x hx).2.1))
    hstrict hA₁ hA₂
  -- Uniform Hessian operator-norm bound K (independent of δ!):
  let K_hess : ℝ := max (1 / ε) (2 * C_upper + 2 * σ) + 1
  have hK_hess : 0 < K_hess := by positivity
  -- Lower bound r_lo on ‖g₁‖, ‖g₂‖, ‖g₁'‖, ‖g₂'‖:
  let r_lo : ℝ := min (t * d₀ / 4) ((1 - t) * d₀ / 4)
  have hr_lo : 0 < r_lo := lt_min (by positivity) (by positivity)
  -- Tolerance on ‖g₁' - g₁‖ and ‖g₂' - g₂‖ so matrixNormalizedPLaplacian changes by < s₀ / (16 * max(t⁻², (1-t)⁻²))
  let W_max : ℝ := max (t⁻¹ ^ 2) ((1 - t)⁻¹ ^ 2)
  have hW_max : 0 < W_max := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let Lip_g : ℝ := 4 * |p - 2| * K_hess / r_lo + 1
  have hLip_g : 0 < Lip_g := by positivity
  let η_grad : ℝ := min (r_lo / 2) (s₀ / (32 * W_max * Lip_g))
  have hη_grad : 0 < η_grad := lt_min (half_pos hr_lo) (by positivity)
  -- Choose r_close > 0 so 2 * σ * r_close < η_grad / 2
  let r_close : ℝ := min (ρ / 2) (η_grad / (8 * σ))
  have hr_close : 0 < r_close := lt_min (half_pos hρ) (by positivity)
  -- Strict maximality on the compact complement Q_out := {(y, z) ∈ closedBall yε ρ × closedBall zε ρ |
  --   y ∉ ball yε r_close ∨ z ∉ ball zε r_close} gives a uniform gap > 0, so for small δ,
  -- any maximizer (y, z) has y ∈ ball yε r_close and z ∈ ball zε r_close!
  let F₀ : Space n × Space n → ℝ := fun q => min (u₁ q.1) (v₁ q.2) - φt (t • q.1 + (1 - t) • q.2)
  have hu₁_cont : Continuous u₁ := by
    have heq : u₁ = fun y => (u₁ y + (M / 2) * ‖y‖ ^ 2) - (M / 2) * ‖y‖ ^ 2 := by funext y; ring
    rw [heq]
    exact hf₁_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hv₁_cont : Continuous v₁ := by
    have heq : v₁ = fun z => (v₁ z + (M / 2) * ‖z‖ ^ 2) - (M / 2) * ‖z‖ ^ 2 := by funext z; ring
    rw [heq]
    exact hf₂_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hF₀_cont : ContinuousOn F₀ (closedBall yε ρ ×ˢ closedBall zε ρ) := by
    have h1 : ContinuousOn (fun q : Space n × Space n => min (u₁ q.1) (v₁ q.2))
        (closedBall yε ρ ×ˢ closedBall zε ρ) :=
      ((hu₁_cont.comp continuous_fst).inf (hv₁_cont.comp continuous_snd)).continuousOn
    have h2 : ContinuousOn (fun q : Space n × Space n => φt (t • q.1 + (1 - t) • q.2))
        (closedBall yε ρ ×ˢ closedBall zε ρ) := by
      refine hφt_U.continuousOn.comp
        ((continuous_fst.const_smul t).add (continuous_snd.const_smul (1 - t))).continuousOn ?_
      intro q hq
      apply (hsub_x _ ?_).1
      rw [mem_closedBall, dist_eq_norm]
      have hy : ‖q.1 - yε‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hq.1
      have hz : ‖q.2 - zε‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hq.2
      have hvec : (t • q.1 + (1 - t) • q.2) - xε = t • (q.1 - yε) + (1 - t) • (q.2 - zε) := by
        dsimp only [xε]; module
      rw [hvec]
      calc ‖t • (q.1 - yε) + (1 - t) • (q.2 - zε)‖
          ≤ ‖t • (q.1 - yε)‖ + ‖(1 - t) • (q.2 - zε)‖ := norm_add_le _ _
        _ = t * ‖q.1 - yε‖ + (1 - t) * ‖q.2 - zε‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht1_pos.le]
        _ ≤ t * ρ + (1 - t) * ρ := by gcongr
        _ ≤ 2 * ρ := by linarith
    exact h1.sub h2
  let Q_out : Set (Space n × Space n) :=
    (closedBall yε ρ ×ˢ closedBall zε ρ) \ (ball yε r_close ×ˢ ball zε r_close)
  have hQ_out_comp : IsCompact Q_out :=
    ((isCompact_closedBall yε ρ).prod (isCompact_closedBall zε ρ)).diff (isOpen_ball.prod isOpen_ball)
  have hgap_out : ∃ g_out : ℝ, 0 < g_out ∧ ∀ q ∈ Q_out, F₀ q ≤ F₀ (yε, zε) - g_out := by
    by_cases hne : Q_out.Nonempty
    · obtain ⟨qm, hqm, hqm_max⟩ := hQ_out_comp.exists_isMaxOn hne (hF₀_cont.mono diff_subset)
      have hqm_ne : qm ≠ (yε, zε) := by
        intro heq; subst heq
        exact hqm.2 ⟨mem_ball_self hr_close, mem_ball_self hr_close⟩
      have hlt : F₀ qm < F₀ (yε, zε) := hstrict qm.1 hqm.1.1 qm.2 hqm.1.2 hqm_ne
      exact ⟨F₀ (yε, zε) - F₀ qm, sub_pos.mpr hlt, fun q hq => by linarith [isMaxOn_iff.mp hqm_max q hq]⟩
    · refine ⟨1, zero_lt_one, fun q hq => (hne ⟨q, hq⟩).elim⟩
  obtain ⟨g_out, hg_out, hQ_out_le⟩ := hgap_out
  -- Choose δ > 0 so small that:
  -- (1) δ < η_grad / 2
  -- (2) δ * (2 * (‖yε‖ + ‖zε‖ + ρ) + 1) < g_out / 2 (forces (y, z) ∈ ball yε r_close × ball zε r_close)
  let B_norm : ℝ := 2 * (‖yε‖ + ‖zε‖ + ρ) + 2
  have hB_norm : 0 < B_norm := by positivity
  let δ : ℝ := min (η_grad / 2) (g_out / (4 * B_norm))
  have hδ : 0 < δ := lt_min (half_pos hη_grad) (by positivity)
  obtain ⟨p₁, p₂, c, y, z, hp₁, hp₂, hc, hy_ball, hz_ball, hy_A₁, hz_A₂, heq_pert,
    hmax_pert, hquad_u, hquad_v⟩ := hgood δ hδ
  -- Verify (y, z) ∈ ball yε r_close × ball zε r_close:
  have hyz_close : y ∈ ball yε r_close ∧ z ∈ ball zε r_close := by
    by_contra hnot
    have hq_out : (y, z) ∈ Q_out :=
      ⟨⟨ball_subset_closedBall (ball_subset_ball (by linarith only [hρ] : ρ / 3 ≤ ρ) hy_ball),
        ball_subset_closedBall (ball_subset_ball (by linarith only [hρ] : ρ / 3 ≤ ρ) hz_ball)⟩,
        fun h => hnot ⟨h.1, h.2⟩⟩
    have hle_out := hQ_out_le (y, z) hq_out
    have hge_pert := hmax_pert yε (mem_closedBall_self hρ.le) zε (mem_closedBall_self hρ.le)
    have hbound_pt (a b : Space n) (ha : a ∈ closedBall b ρ) (hp : ‖p₁‖ < δ) :
        |inner ℝ p₁ a| ≤ δ * (‖b‖ + ρ) := by
      have ha_norm : ‖a‖ ≤ ‖b‖ + ρ := by
        have h1 : ‖a - b‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using ha
        have h2 := norm_add_le (a - b) b; rw [sub_add_cancel] at h2; linarith only [h1, h2]
      calc |inner ℝ p₁ a| ≤ ‖p₁‖ * ‖a‖ := abs_real_inner_le_norm _ _
        _ ≤ δ * (‖b‖ + ρ) := mul_le_mul hp.le ha_norm (norm_nonneg _) hδ.le
    have hbound_pt2 (a b : Space n) (ha : a ∈ closedBall b ρ) (hp : ‖p₂‖ < δ) :
        |inner ℝ p₂ a| ≤ δ * (‖b‖ + ρ) := by
      have ha_norm : ‖a‖ ≤ ‖b‖ + ρ := by
        have h1 : ‖a - b‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using ha
        have h2 := norm_add_le (a - b) b; rw [sub_add_cancel] at h2; linarith only [h1, h2]
      calc |inner ℝ p₂ a| ≤ ‖p₂‖ * ‖a‖ := abs_real_inner_le_norm _ _
        _ ≤ δ * (‖b‖ + ρ) := mul_le_mul hp.le ha_norm (norm_nonneg _) hδ.le
    have h1 := hbound_pt y yε hq_out.1.1 hp₁
    have h2 := hbound_pt yε yε (mem_closedBall_self hρ.le) hp₁
    have h3 := hbound_pt2 z zε hq_out.1.2 hp₂
    have h4 := hbound_pt2 zε zε (mem_closedBall_self hρ.le) hp₂
    have hδ_y : δ * (‖yε‖ + ρ) ≤ δ * (‖yε‖ + ‖zε‖ + ρ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [norm_nonneg zε]) hδ.le
    have hδ_z : δ * (‖zε‖ + ρ) + δ ≤ δ * (‖yε‖ + ‖zε‖ + ρ + 1) := by
      have hmul : δ * (‖zε‖ + ρ + 1) ≤ δ * (‖yε‖ + ‖zε‖ + ρ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [norm_nonneg yε]) hδ.le
      have heq : δ * (‖zε‖ + ρ) + δ = δ * (‖zε‖ + ρ + 1) := by ring
      linarith only [hmul, heq]
    have hpert_upper : min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) ≤
        min (u₁ y) (v₁ z) + δ * (‖yε‖ + ‖zε‖ + ρ + 1) := by
      have ha : u₁ y + inner ℝ p₁ y ≤ u₁ y + δ * (‖yε‖ + ‖zε‖ + ρ + 1) := by
        linarith only [(abs_le.mp h1).2, hδ_y]
      have hb : v₁ z + inner ℝ p₂ z + c ≤ v₁ z + δ * (‖yε‖ + ‖zε‖ + ρ + 1) := by
        linarith only [(abs_le.mp h3).2, (abs_le.mp hc.le).2, hδ_z]
      exact (min_le_min ha hb).trans_eq (min_add_add_right _ _ _)
    have hpert_lower : min (u₁ yε) (v₁ zε) - δ * (‖yε‖ + ‖zε‖ + ρ + 1) ≤
        min (u₁ yε + inner ℝ p₁ yε) (v₁ zε + inner ℝ p₂ zε + c) := by
      have ha : u₁ yε - δ * (‖yε‖ + ‖zε‖ + ρ + 1) ≤ u₁ yε + inner ℝ p₁ yε := by
        linarith only [(abs_le.mp h2).1, hδ_y]
      have hb : v₁ zε - δ * (‖yε‖ + ‖zε‖ + ρ + 1) ≤ v₁ zε + inner ℝ p₂ zε + c := by
        linarith only [(abs_le.mp h4).1, (abs_le.mp hc.le).1, hδ_z]
      exact (min_sub_sub_right _ _ _).symm.le.trans (min_le_min ha hb)
    have hδ_small : 2 * δ * (‖yε‖ + ‖zε‖ + ρ + 1) < g_out := by
      have hδ2 : δ ≤ g_out / (4 * B_norm) := min_le_right _ _
      have hB_ge : 2 * (‖yε‖ + ‖zε‖ + ρ + 1) ≤ B_norm := by dsimp only [B_norm]; linarith only
      calc 2 * δ * (‖yε‖ + ‖zε‖ + ρ + 1)
          = δ * (2 * (‖yε‖ + ‖zε‖ + ρ + 1)) := by ring
        _ ≤ (g_out / (4 * B_norm)) * B_norm := mul_le_mul hδ2 hB_ge (by positivity) (by positivity)
        _ = g_out / 4 := by field_simp [hB_norm.ne']
        _ < g_out := by linarith only [hg_out]
    dsimp only [F₀] at hle_out
    linarith only [hle_out, hge_pert, hpert_upper, hpert_lower, hδ_small]
  -- Extract second-order Taylor expansions of uε at y and vε at z from A₁, A₂
  obtain ⟨hdf₁, Af₁, htf₁⟩ := hy_A₁
  obtain ⟨hdf₂, Af₂, htf₂⟩ := hz_A₂
  let gf₁ : Space n := gradient (fun y' => uε y' + (1 / (2 * ε)) * ‖y'‖ ^ 2) y
  let gf₂ : Space n := gradient (fun z' => vε z' + (1 / (2 * ε)) * ‖z'‖ ^ 2) z
  have htuε : HasSecondOrderTaylorAt uε (gf₁ - (1 / ε) • y)
      (Af₁ - (1 / ε) • ContinuousLinearMap.id ℝ (Space n)) y := by
    have h := htf₁.sub_quad (1 / ε)
    have heq : (fun y' => uε y' + 1 / (2 * ε) * ‖y'‖ ^ 2 - (1 / ε) / 2 * ‖y'‖ ^ 2) = uε := by
      funext y'; ring
    rwa [heq] at h
  have htvε : HasSecondOrderTaylorAt vε (gf₂ - (1 / ε) • z)
      (Af₂ - (1 / ε) • ContinuousLinearMap.id ℝ (Space n)) z := by
    have h := htf₂.sub_quad (1 / ε)
    have heq : (fun z' => vε z' + 1 / (2 * ε) * ‖z'‖ ^ 2 - (1 / ε) / 2 * ‖z'‖ ^ 2) = vε := by
      funext z'; ring
    rwa [heq] at h
  let g₁' : Space n := gf₁ - (1 / ε) • y
  let A₁' : Space n →L[ℝ] Space n := Af₁ - (1 / ε) • ContinuousLinearMap.id ℝ (Space n)
  let g₂' : Space n := gf₂ - (1 / ε) • z
  let A₂' : Space n →L[ℝ] Space n := Af₂ - (1 / ε) • ContinuousLinearMap.id ℝ (Space n)
  -- Shifted Taylor expansions for u_pert(y') = u₁ y' + ⟪p₁, y'⟫ and v_pert(z') = v₁ z' + ⟪p₂, z'⟫ + c
  let u_pert : Space n → ℝ := fun y' => u₁ y' + inner ℝ p₁ y'
  let v_pert : Space n → ℝ := fun z' => v₁ z' + inner ℝ p₂ z' + c
  let g₁ : Space n := g₁' - (2 * σ) • (y - yε) + p₁
  let A₁ : Space n →L[ℝ] Space n := A₁' - (2 * σ) • ContinuousLinearMap.id ℝ (Space n)
  let g₂ : Space n := g₂' - (2 * σ) • (z - zε) + p₂
  let A₂ : Space n →L[ℝ] Space n := A₂' - (2 * σ) • ContinuousLinearMap.id ℝ (Space n)
  have htu_pert : HasSecondOrderTaylorAt u_pert g₁ A₁ y := by
    simpa only [u_pert, u₁, add_zero] using htuε.sub_quad_add_lin_const σ yε p₁ 0
  have htv_pert : HasSecondOrderTaylorAt v_pert g₂ A₂ z := by
    simpa only [v_pert, v₁] using htvε.sub_quad_add_lin_const σ zε p₂ c
  -- Uniform operator norm bounds ‖A₁'‖ ≤ K_hess and ‖A₂'‖ ≤ K_hess:
  have hA₁'_psd : ∀ w : Space n, -(1 / ε) * ‖w‖ ^ 2 ≤ inner ℝ (A₁' w) w := by
    intro w
    have hsub := IsSubgradient.of_hasFDerivAt hfuε_conv hdf₁.hasFDerivAt
    have hpsd := htf₁.psd_of_convexOn hfuε_conv hsub w
    dsimp only [A₁']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    linarith
  have hA₂'_psd : ∀ w : Space n, -(1 / ε) * ‖w‖ ^ 2 ≤ inner ℝ (A₂' w) w := by
    intro w
    have hsub := IsSubgradient.of_hasFDerivAt hfvε_conv hdf₂.hasFDerivAt
    have hpsd := htf₂.psd_of_convexOn hfvε_conv hsub w
    dsimp only [A₂']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    linarith
  -- Upper quadratic bound on A₁', A₂' from hquad_u, hquad_v:
  have hA₁'_upper : ∀ w : Space n, inner ℝ (A₁' w) w ≤ (2 * C_upper + 2 * σ) * ‖w‖ ^ 2 := by
    -- f₁(y') = u₁ y' + (M/2)‖y'‖² has HasSecondOrderTaylorAt with Hessian A₁' + (1/ε)•id
    -- (since u₁ y' + (M/2)‖y'‖² = uε y' + (1/(2ε))‖y'‖² + 2σ⟪yε, y'⟫ - σ‖yε‖²!)
    have htf₁_M : HasSecondOrderTaylorAt (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2)
        (gf₁ + (2 * σ) • yε) Af₁ y := by
      refine ⟨htf₁.1, htf₁.2.congr' (Eventually.of_forall fun y' => ?_) (Eventually.of_forall fun _ => rfl)⟩
      dsimp only
      rw [hu₁_id y', hu₁_id y, inner_add_left, real_inner_smul_left, inner_sub_right yε y' y]
      ring
    have hsubg : IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y (gf₁ + (2 * σ) • yε) := by
      have hfd1 : HasFDerivAt (fun y' => uε y' + (1 / (2 * ε)) * ‖y'‖ ^ 2) (toDual ℝ (Space n) gf₁) y :=
        hdf₁.hasGradientAt.hasFDerivAt
      have hfd2 : HasFDerivAt (fun y' => (2 * σ) * inner ℝ yε y') (toDual ℝ (Space n) ((2 * σ) • yε)) y := by
        have hlin := (toDual ℝ (Space n) ((2 * σ) • yε)).hasFDerivAt (x := y)
        refine hlin.congr_of_eventuallyEq (Eventually.of_forall fun y' => ?_)
        rw [toDual_apply_apply, real_inner_smul_left]
      have hfd : HasFDerivAt (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2)
          (toDual ℝ (Space n) (gf₁ + (2 * σ) • yε)) y := by
        have hsum := (hfd1.add hfd2).sub_const (σ * ‖yε‖ ^ 2)
        rw [← map_add] at hsum
        exact hsum.congr_of_eventuallyEq (Eventually.of_forall hu₁_id)
      simpa using IsSubgradient.of_hasFDerivAt hf₁_conv hfd
    intro w
    by_cases hw0 : w = 0
    · subst hw0; simp
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hupper_f1 := hquad_u (gf₁ + (2 * σ) • yε) hsubg
    -- From Taylor expansion of f₁: (1/2)⟪Af₁ w, w⟫ ≤ C_upper ‖w‖², so ⟪Af₁ w, w⟫ ≤ 2 C_upper ‖w‖²,
    -- hence ⟪A₁' w, w⟫ = ⟪Af₁ w, w⟫ - (1/ε)‖w‖² ≤ 2 C_upper ‖w‖² ≤ (2 C_upper + 2 σ) ‖w‖²!
    have hAf1_le : inner ℝ (Af₁ w) w ≤ 2 * C_upper * ‖w‖ ^ 2 := by
      by_contra hbad; push Not at hbad
      let α : ℝ := (inner ℝ (Af₁ w) w - 2 * C_upper * ‖w‖ ^ 2) / (4 * ‖w‖ ^ 2)
      have hα : 0 < α := div_pos (by linarith) (by positivity)
      have hlo := htf₁_M.2; rw [Asymptotics.isLittleO_iff] at hlo
      obtain ⟨r', hr', hbr'⟩ := Metric.eventually_nhds_iff.mp (hlo hα)
      let s : ℝ := min (r' / (2 * ‖w‖)) (ρ₀ / (2 * ‖w‖))
      have hs : 0 < s := lt_min (by positivity) (by positivity)
      have hdist : dist (y + s • w) y < r' := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
        have : s ≤ r' / (2 * ‖w‖) := min_le_left _ _
        calc s * ‖w‖ ≤ (r' / (2 * ‖w‖)) * ‖w‖ := mul_le_mul_of_nonneg_right this hw_pos.le
          _ = r' / 2 := by field_simp [hw_pos.ne']
          _ < r' := half_lt_self hr'
      have hmem : y + s • w ∈ closedBall y ρ₀ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
        have : s ≤ ρ₀ / (2 * ‖w‖) := min_le_right _ _
        calc s * ‖w‖ ≤ (ρ₀ / (2 * ‖w‖)) * ‖w‖ := mul_le_mul_of_nonneg_right this hw_pos.le
          _ = ρ₀ / 2 := by field_simp [hw_pos.ne']
          _ ≤ ρ₀ := (half_lt_self hρ₀).le
      have hq := hupper_f1 (y + s • w) hmem
      have hb := hbr' hdist
      simp only [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
        map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
        Real.norm_of_nonneg hs.le] at hq hb
      have hb1 := (abs_le.mp hb).1
      have hα_eq : α * (s * ‖w‖) ^ 2 = (1 / 4 : ℝ) * s ^ 2 * (inner ℝ (Af₁ w) w - 2 * C_upper * ‖w‖ ^ 2) := by
        dsimp only [α]; field_simp [hw_pos.ne']
      have hpos : 0 < (1 / 4 : ℝ) * s ^ 2 * (inner ℝ (Af₁ w) w - 2 * C_upper * ‖w‖ ^ 2) :=
        mul_pos (by positivity) (by linarith)
      nlinarith only [hq, hb1, hα_eq, hpos]
    dsimp only [A₁']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
    nlinarith only [hAf1_le, hσ, hεinv, sq_nonneg ‖w‖]
  have hA₂'_upper : ∀ w : Space n, inner ℝ (A₂' w) w ≤ (2 * C_upper + 2 * σ) * ‖w‖ ^ 2 := by
    have htf₂_M : HasSecondOrderTaylorAt (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2)
        (gf₂ + (2 * σ) • zε) Af₂ z := by
      refine ⟨htf₂.1, htf₂.2.congr' (Eventually.of_forall fun z' => ?_) (Eventually.of_forall fun _ => rfl)⟩
      dsimp only
      rw [hv₁_id z', hv₁_id z, inner_add_left, real_inner_smul_left, inner_sub_right zε z' z]
      ring
    have hsubg : IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z (gf₂ + (2 * σ) • zε) := by
      have hfd1 : HasFDerivAt (fun z' => vε z' + (1 / (2 * ε)) * ‖z'‖ ^ 2) (toDual ℝ (Space n) gf₂) z :=
        hdf₂.hasGradientAt.hasFDerivAt
      have hfd2 : HasFDerivAt (fun z' => (2 * σ) * inner ℝ zε z') (toDual ℝ (Space n) ((2 * σ) • zε)) z := by
        have hlin := (toDual ℝ (Space n) ((2 * σ) • zε)).hasFDerivAt (x := z)
        refine hlin.congr_of_eventuallyEq (Eventually.of_forall fun z' => ?_)
        rw [toDual_apply_apply, real_inner_smul_left]
      have hfd : HasFDerivAt (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2)
          (toDual ℝ (Space n) (gf₂ + (2 * σ) • zε)) z := by
        have hsum := (hfd1.add hfd2).sub_const (σ * ‖zε‖ ^ 2)
        rw [← map_add] at hsum
        exact hsum.congr_of_eventuallyEq (Eventually.of_forall hv₁_id)
      simpa using IsSubgradient.of_hasFDerivAt hf₂_conv hfd
    intro w
    by_cases hw0 : w = 0
    · subst hw0; simp
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hupper_f2 := hquad_v (gf₂ + (2 * σ) • zε) hsubg
    have hAf2_le : inner ℝ (Af₂ w) w ≤ 2 * C_upper * ‖w‖ ^ 2 := by
      by_contra hbad; push Not at hbad
      let α : ℝ := (inner ℝ (Af₂ w) w - 2 * C_upper * ‖w‖ ^ 2) / (4 * ‖w‖ ^ 2)
      have hα : 0 < α := div_pos (by linarith) (by positivity)
      have hlo := htf₂_M.2; rw [Asymptotics.isLittleO_iff] at hlo
      obtain ⟨r', hr', hbr'⟩ := Metric.eventually_nhds_iff.mp (hlo hα)
      let s : ℝ := min (r' / (2 * ‖w‖)) (ρ₀ / (2 * ‖w‖))
      have hs : 0 < s := lt_min (by positivity) (by positivity)
      have hdist : dist (z + s • w) z < r' := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
        have : s ≤ r' / (2 * ‖w‖) := min_le_left _ _
        calc s * ‖w‖ ≤ (r' / (2 * ‖w‖)) * ‖w‖ := mul_le_mul_of_nonneg_right this hw_pos.le
          _ = r' / 2 := by field_simp [hw_pos.ne']
          _ < r' := half_lt_self hr'
      have hmem : z + s • w ∈ closedBall z ρ₀ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
        have : s ≤ ρ₀ / (2 * ‖w‖) := min_le_right _ _
        calc s * ‖w‖ ≤ (ρ₀ / (2 * ‖w‖)) * ‖w‖ := mul_le_mul_of_nonneg_right this hw_pos.le
          _ = ρ₀ / 2 := by field_simp [hw_pos.ne']
          _ ≤ ρ₀ := (half_lt_self hρ₀).le
      have hq := hupper_f2 (z + s • w) hmem
      have hb := hbr' hdist
      simp only [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
        map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
        Real.norm_of_nonneg hs.le] at hq hb
      have hb1 := (abs_le.mp hb).1
      have hα_eq : α * (s * ‖w‖) ^ 2 = (1 / 4 : ℝ) * s ^ 2 * (inner ℝ (Af₂ w) w - 2 * C_upper * ‖w‖ ^ 2) := by
        dsimp only [α]; field_simp [hw_pos.ne']
      have hpos : 0 < (1 / 4 : ℝ) * s ^ 2 * (inner ℝ (Af₂ w) w - 2 * C_upper * ‖w‖ ^ 2) :=
        mul_pos (by positivity) (by linarith)
      nlinarith only [hq, hb1, hα_eq, hpos]
    dsimp only [A₂']
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hεinv : 0 < 1 / ε := one_div_pos.mpr hε
    nlinarith only [hAf2_le, hσ, hεinv, sq_nonneg ‖w‖]
  have hA₁'_norm : ‖A₁'‖ ≤ K_hess :=
    opNorm_le_of_symmetric_quad_bound htuε.1 hK_hess.le fun w => abs_le.mpr
      ⟨by have h1 := hA₁'_psd w; have h2 : 1 / ε ≤ K_hess := by dsimp only [K_hess]; linarith only [le_max_left (1 / ε) (2 * C_upper + 2 * σ)]
          nlinarith only [h1, h2, sq_nonneg ‖w‖],
       by have h1 := hA₁'_upper w; have h2 : 2 * C_upper + 2 * σ ≤ K_hess := by dsimp only [K_hess]; linarith only [le_max_right (1 / ε) (2 * C_upper + 2 * σ)]
          nlinarith only [h1, h2, sq_nonneg ‖w‖]⟩
  have hA₂'_norm : ‖A₂'‖ ≤ K_hess :=
    opNorm_le_of_symmetric_quad_bound htvε.1 hK_hess.le fun w => abs_le.mpr
      ⟨by have h1 := hA₂'_psd w; have h2 : 1 / ε ≤ K_hess := by dsimp only [K_hess]; linarith only [le_max_left (1 / ε) (2 * C_upper + 2 * σ)]
          nlinarith only [h1, h2, sq_nonneg ‖w‖],
       by have h1 := hA₂'_upper w; have h2 : 2 * C_upper + 2 * σ ≤ K_hess := by dsimp only [K_hess]; linarith only [le_max_right (1 / ε) (2 * C_upper + 2 * σ)]
          nlinarith only [h1, h2, sq_nonneg ‖w‖]⟩
  -- Local touching of min(u_pert, v_pert) ≤ φt + C_shift near (y, z)
  let x : Space n := t • y + (1 - t) • z
  have hx_cl : x ∈ closedBall xε (2 * ρ) := by
    rw [mem_closedBall, dist_eq_norm]
    have hy : ‖y - yε‖ < ρ / 3 := by simpa [mem_ball, dist_eq_norm] using hy_ball
    have hz : ‖z - zε‖ < ρ / 3 := by simpa [mem_ball, dist_eq_norm] using hz_ball
    have hvec : x - xε = t • (y - yε) + (1 - t) • (z - zε) := by dsimp only [x, xε]; module
    rw [hvec]
    calc ‖t • (y - yε) + (1 - t) • (z - zε)‖
        ≤ ‖t • (y - yε)‖ + ‖(1 - t) • (z - zε)‖ := norm_add_le _ _
      _ = t * ‖y - yε‖ + (1 - t) * ‖z - zε‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht1_pos.le]
      _ ≤ t * (ρ / 3) + (1 - t) * (ρ / 3) := by gcongr
      _ ≤ 2 * ρ := by linarith
  have hx_prop := hsub_x x hx_cl
  have hgφ_ne : gradient φt x ≠ 0 := norm_pos_iff.mp (lt_trans (half_pos hd₀) hx_prop.2.1)
  have hφt_at_x : ContDiffAt ℝ 2 φt x := hφt_U.contDiffAt (hU.mem_nhds hx_prop.1)
  let C_shift : ℝ := u_pert y - φt x
  let φ_sh : Space n → ℝ := fun x' => φt x' + C_shift
  have hφ_sh_at : ContDiffAt ℝ 2 φ_sh x := hφt_at_x.add contDiffAt_const
  have hgrad_sh : gradient φ_sh x = gradient φt x := BMCompactAnalytic.gradient_add_const φt C_shift x
  have hlap_sh : normalizedPLaplacian p φ_sh x = normalizedPLaplacian p φt x :=
    BMCompactAnalytic.normalizedPLaplacian_add_const p φt C_shift x
  have htouch_ev : ∀ᶠ q : Space n × Space n in 𝓝 (y, z),
      min (u_pert q.1) (v_pert q.2) ≤ φ_sh (t • q.1 + (1 - t) • q.2) := by
    have h1 : closedBall yε ρ ∈ 𝓝 y :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds (ball_subset_ball (by linarith : ρ / 3 ≤ ρ) hy_ball))
        ball_subset_closedBall
    have h2 : closedBall zε ρ ∈ 𝓝 z :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds (ball_subset_ball (by linarith : ρ / 3 ≤ ρ) hz_ball))
        ball_subset_closedBall
    rw [nhds_prod_eq]
    filter_upwards [Filter.prod_mem_prod h1 h2] with q hq
    have hm := hmax_pert q.1 hq.1 q.2 hq.2
    dsimp only [u_pert, v_pert, φ_sh, C_shift, x] at hm ⊢
    rw [heq_pert, min_self] at hm
    linarith
  -- First-order alignment gives g₁ ≠ 0, g₂ ≠ 0, ‖g₁‖ ≥ t * d₀ / 2, ‖g₂‖ ≥ (1 - t) * d₀ / 2,
  -- and t * (d/a)³ ≤ t⁻², (1-t) * (d/b)³ ≤ (1-t)⁻²!
  have hfirst_order : ∀ h k : Space n,
      min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤
        t * inner ℝ (gradient φt x) h + (1 - t) * inner ℝ (gradient φt x) k := by
    intro h k
    have hgrad_u : HasGradientAt u_pert g₁ y := by
      rw [hasGradientAt_iff_isLittleO]
      have hsq_o : (fun y' : Space n => ‖y' - y‖ ^ 2) =o[𝓝 y] (fun y' : Space n => y' - y) := by
        rw [Asymptotics.isLittleO_iff]; intro c' hc'
        filter_upwards [Metric.ball_mem_nhds y hc'] with y' hy'
        have hd : ‖y' - y‖ < c' := by simpa [mem_ball, dist_eq_norm] using hy'
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
      have h2 : (fun y' => (1 / 2 : ℝ) * inner ℝ (A₁ (y' - y)) (y' - y)) =o[𝓝 y] (fun y' => y' - y) := by
        rw [Asymptotics.isLittleO_iff]; intro c' hc'
        let d' : ℝ := c' / (‖A₁‖ + 1)
        filter_upwards [Metric.ball_mem_nhds y (show 0 < d' by positivity)] with y' hy'
        have hd : ‖y' - y‖ < d' := by simpa [mem_ball, dist_eq_norm] using hy'
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        calc (1 / 2 : ℝ) * |inner ℝ (A₁ (y' - y)) (y' - y)|
            ≤ (1 / 2 : ℝ) * (‖A₁ (y' - y)‖ * ‖y' - y‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
          _ ≤ (1 / 2 : ℝ) * ((‖A₁‖ * ‖y' - y‖) * ‖y' - y‖) := by gcongr; exact A₁.le_opNorm _
          _ = ((1 / 2 : ℝ) * ‖A₁‖ * ‖y' - y‖) * ‖y' - y‖ := by ring
          _ ≤ ((‖A₁‖ + 1) * d') * ‖y' - y‖ :=
              mul_le_mul_of_nonneg_right (by nlinarith only [hd, norm_nonneg A₁, norm_nonneg (y' - y)]) (norm_nonneg _)
          _ = c' * ‖y' - y‖ := by dsimp only [d']; field_simp [(show (0 : ℝ) < ‖A₁‖ + 1 by positivity).ne']
      refine (htu_pert.2.trans hsq_o |>.add h2).congr' (Eventually.of_forall fun y' => ?_) (Eventually.of_forall fun _ => rfl)
      ring
    have hgrad_v : HasGradientAt v_pert g₂ z := by
      rw [hasGradientAt_iff_isLittleO]
      have hsq_o : (fun z' : Space n => ‖z' - z‖ ^ 2) =o[𝓝 z] (fun z' : Space n => z' - z) := by
        rw [Asymptotics.isLittleO_iff]; intro c' hc'
        filter_upwards [Metric.ball_mem_nhds z hc'] with z' hz'
        have hd : ‖z' - z‖ < c' := by simpa [mem_ball, dist_eq_norm] using hz'
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
      have h2 : (fun z' => (1 / 2 : ℝ) * inner ℝ (A₂ (z' - z)) (z' - z)) =o[𝓝 z] (fun z' => z' - z) := by
        rw [Asymptotics.isLittleO_iff]; intro c' hc'
        let d' : ℝ := c' / (‖A₂‖ + 1)
        filter_upwards [Metric.ball_mem_nhds z (show 0 < d' by positivity)] with z' hz'
        have hd : ‖z' - z‖ < d' := by simpa [mem_ball, dist_eq_norm] using hz'
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        calc (1 / 2 : ℝ) * |inner ℝ (A₂ (z' - z)) (z' - z)|
            ≤ (1 / 2 : ℝ) * (‖A₂ (z' - z)‖ * ‖z' - z‖) :=
              mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
          _ ≤ (1 / 2 : ℝ) * ((‖A₂‖ * ‖z' - z‖) * ‖z' - z‖) := by gcongr; exact A₂.le_opNorm _
          _ = ((1 / 2 : ℝ) * ‖A₂‖ * ‖z' - z‖) * ‖z' - z‖ := by ring
          _ ≤ ((‖A₂‖ + 1) * d') * ‖z' - z‖ :=
              mul_le_mul_of_nonneg_right (by nlinarith only [hd, norm_nonneg A₂, norm_nonneg (z' - z)]) (norm_nonneg _)
          _ = c' * ‖z' - z‖ := by dsimp only [d']; field_simp [(show (0 : ℝ) < ‖A₂‖ + 1 by positivity).ne']
      refine (htv_pert.2.trans hsq_o |>.add h2).congr' (Eventually.of_forall fun z' => ?_) (Eventually.of_forall fun _ => rfl)
      ring
    have hd_u : Tendsto (fun s : ℝ => (u_pert (y + s • h) - u_pert y) / s) (𝓝[>] 0) (𝓝 (inner ℝ g₁ h)) := by
      have hl : HasDerivAt (fun s : ℝ => y + s • h) h 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add y
      have hd := (by simpa using hgrad_u.hasFDerivAt :
        HasFDerivAt u_pert (toDual ℝ (Space n) g₁) (y + (0 : ℝ) • h)).comp_hasDerivAt 0 hl
      rw [toDual_apply_apply] at hd
      simpa [div_eq_inv_mul] using hd.tendsto_slope_zero_right
    have hd_v : Tendsto (fun s : ℝ => (v_pert (z + s • k) - v_pert z) / s) (𝓝[>] 0) (𝓝 (inner ℝ g₂ k)) := by
      have hl : HasDerivAt (fun s : ℝ => z + s • k) k 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add z
      have hd := (by simpa using hgrad_v.hasFDerivAt :
        HasFDerivAt v_pert (toDual ℝ (Space n) g₂) (z + (0 : ℝ) • k)).comp_hasDerivAt 0 hl
      rw [toDual_apply_apply] at hd
      simpa [div_eq_inv_mul] using hd.tendsto_slope_zero_right
    have hd_φ : Tendsto (fun s : ℝ => (φ_sh (x + s • (t • h + (1 - t) • k)) - φ_sh x) / s)
        (𝓝[>] 0) (𝓝 (t * inner ℝ (gradient φt x) h + (1 - t) * inner ℝ (gradient φt x) k)) := by
      have hl : HasDerivAt (fun s : ℝ => x + s • (t • h + (1 - t) • k)) (t • h + (1 - t) • k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (t • h + (1 - t) • k)).const_add x
      have hd := (by simpa using (hφ_sh_at.differentiableAt (by norm_num)).hasGradientAt.hasFDerivAt :
        HasFDerivAt φ_sh (toDual ℝ (Space n) (gradient φ_sh x))
          (x + (0 : ℝ) • (t • h + (1 - t) • k))).comp_hasDerivAt 0 hl
      rw [toDual_apply_apply, hgrad_sh, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hd
      simpa [div_eq_inv_mul] using hd.tendsto_slope_zero_right
    have hcont_path : ContinuousAt (fun s : ℝ => (y + s • h, z + s • k)) 0 := by
      have h1 : Continuous (fun s : ℝ => (y + s • h, z + s • k)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).prodMk
          (continuous_const.add (continuous_id.smul continuous_const))
      exact h1.continuousAt
    have hev_s : ∀ᶠ s : ℝ in 𝓝[>] 0,
        min ((u_pert (y + s • h) - u_pert y) / s) ((v_pert (z + s • k) - v_pert z) / s) ≤
          (φ_sh (x + s • (t • h + (1 - t) • k)) - φ_sh x) / s := by
      have hpath : ∀ᶠ s : ℝ in 𝓝[>] 0,
          min (u_pert (y + s • h)) (v_pert (z + s • k)) ≤
            φ_sh (t • (y + s • h) + (1 - t) • (z + s • k)) := by
        have hct : Tendsto (fun s : ℝ => (y + s • h, z + s • k)) (𝓝[>] 0) (𝓝 (y, z)) := by
          have h0 : (y + (0 : ℝ) • h, z + (0 : ℝ) • k) = (y, z) := by simp
          exact h0 ▸ (hcont_path.tendsto.mono_left nhdsWithin_le_nhds)
        exact hct.eventually htouch_ev
      filter_upwards [self_mem_nhdsWithin, hpath] with s (hs : 0 < s) hts
      have hblend : t • (y + s • h) + (1 - t) • (z + s • k) = x + s • (t • h + (1 - t) • k) := by
        dsimp only [x]; module
      rw [hblend] at hts
      have hφx : φ_sh x = u_pert y := by dsimp only [φ_sh, C_shift]; ring
      have hvx : v_pert z = u_pert y := heq_pert.symm
      rw [hvx, hφx]
      rcases le_total (u_pert (y + s • h)) (v_pert (z + s • k)) with hle | hle
      · rw [min_eq_left hle] at hts
        exact (min_le_left _ _).trans (div_le_div_of_nonneg_right (sub_le_sub_right hts (u_pert y)) hs.le)
      · rw [min_eq_right hle] at hts
        exact (min_le_right _ _).trans (div_le_div_of_nonneg_right (sub_le_sub_right hts (u_pert y)) hs.le)
    exact le_of_tendsto_of_tendsto (hd_u.min hd_v) hd_φ hev_s
  obtain ⟨a, b, ha, hb, hg₁_ν, hg₂_ν, hgφ_ν, hrecip⟩ :=
    first_order_min_alignment ht ht1 hgφ_ne hfirst_order
  have hν_norm : ‖(-(‖gradient φt x‖⁻¹)) • gradient φt x‖ = 1 := by
    have hd_pos : 0 < ‖gradient φt x‖ := norm_pos_iff.mpr hgφ_ne
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hd_pos), inv_mul_cancel₀ hd_pos.ne']
  have ha_eq : ‖g₁‖ = a := by
    rw [hg₁_ν, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ha, hν_norm, mul_one]
  have hb_eq : ‖g₂‖ = b := by
    rw [hg₂_ν, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hb, hν_norm, mul_one]
  have hg₁_ne : g₁ ≠ 0 := norm_pos_iff.mp (ha_eq ▸ ha)
  have hg₂_ne : g₂ ≠ 0 := norm_pos_iff.mp (hb_eq ▸ hb)
  -- Bounds on a, b, and weights t*(d/a)³, (1-t)*(d/b)³:
  have hd_pos : 0 < ‖gradient φt x‖ := norm_pos_iff.mpr hgφ_ne
  have hta_lt : t / a < 1 / ‖gradient φt x‖ := by
    have : 0 < (1 - t) / b := div_pos ht1_pos hb
    linarith
  have htb_lt : (1 - t) / b < 1 / ‖gradient φt x‖ := by
    have : 0 < t / a := div_pos ht ha
    linarith
  have hda_lt : ‖gradient φt x‖ / a < t⁻¹ := by
    rw [div_lt_iff₀ ha]
    have h1 : t * ‖gradient φt x‖ < a := by
      have := (div_lt_div_iff₀ ha hd_pos).mp hta_lt; linarith
    have : ‖gradient φt x‖ < t⁻¹ * a := by
      calc ‖gradient φt x‖ = t⁻¹ * (t * ‖gradient φt x‖) := by field_simp [ht.ne']
        _ < t⁻¹ * a := mul_lt_mul_of_pos_left h1 (inv_pos.mpr ht)
    linarith
  have hdb_lt : ‖gradient φt x‖ / b < (1 - t)⁻¹ := by
    rw [div_lt_iff₀ hb]
    have h1 : (1 - t) * ‖gradient φt x‖ < b := by
      have := (div_lt_div_iff₀ hb hd_pos).mp htb_lt; linarith
    have : ‖gradient φt x‖ < (1 - t)⁻¹ * b := by
      calc ‖gradient φt x‖ = (1 - t)⁻¹ * ((1 - t) * ‖gradient φt x‖) := by field_simp [ht1_pos.ne']
        _ < (1 - t)⁻¹ * b := mul_lt_mul_of_pos_left h1 (inv_pos.mpr ht1_pos)
    linarith
  have hw₁_le : t * (‖gradient φt x‖ / a) ^ 3 ≤ t⁻¹ ^ 2 := by
    have hda_nn : 0 ≤ ‖gradient φt x‖ / a := by positivity
    calc t * (‖gradient φt x‖ / a) ^ 3
        ≤ t * (t⁻¹) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hda_nn hda_lt.le 3) ht.le
      _ = t⁻¹ ^ 2 := by field_simp [ht.ne']
  have hw₂_le : (1 - t) * (‖gradient φt x‖ / b) ^ 3 ≤ (1 - t)⁻¹ ^ 2 := by
    have hdb_nn : 0 ≤ ‖gradient φt x‖ / b := by positivity
    calc (1 - t) * (‖gradient φt x‖ / b) ^ 3
        ≤ (1 - t) * ((1 - t)⁻¹) ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdb_nn hdb_lt.le 3) ht1_pos.le
      _ = (1 - t)⁻¹ ^ 2 := by field_simp [ht1_pos.ne']
  -- Lower bounds ‖g₁‖ ≥ 2 * r_lo and ‖g₂‖ ≥ 2 * r_lo, and ‖g₁ - g₁'‖ < η_grad ≤ r_lo / 2
  have hg₁_ge : 2 * r_lo ≤ ‖g₁‖ := by
    rw [ha_eq]
    have h1 : t * ‖gradient φt x‖ < a := by
      have := (div_lt_div_iff₀ ha hd_pos).mp hta_lt; linarith
    have h2 : t * (d₀ / 2) < t * ‖gradient φt x‖ := mul_lt_mul_of_pos_left hx_prop.2.1 ht
    have h3 : r_lo ≤ t * d₀ / 4 := min_le_left _ _
    linarith
  have hg₂_ge : 2 * r_lo ≤ ‖g₂‖ := by
    rw [hb_eq]
    have h1 : (1 - t) * ‖gradient φt x‖ < b := by
      have := (div_lt_div_iff₀ hb hd_pos).mp htb_lt; linarith
    have h2 : (1 - t) * (d₀ / 2) < (1 - t) * ‖gradient φt x‖ := mul_lt_mul_of_pos_left hx_prop.2.1 ht1_pos
    have h3 : r_lo ≤ (1 - t) * d₀ / 4 := min_le_right _ _
    linarith
  have hg₁_diff : ‖g₁ - g₁'‖ < η_grad := by
    have hvec : g₁ - g₁' = p₁ - (2 * σ) • (y - yε) := by dsimp only [g₁]; abel
    rw [hvec]
    have hy_c : ‖y - yε‖ < r_close := by simpa [mem_ball, dist_eq_norm] using hyz_close.1
    have h1 : ‖p₁‖ < η_grad / 2 := lt_of_lt_of_le hp₁ (min_le_left _ _)
    have h2 : ‖(2 * σ) • (y - yε)‖ < η_grad / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * σ)]
      have hr : r_close ≤ η_grad / (8 * σ) := min_le_right _ _
      calc (2 * σ) * ‖y - yε‖ < (2 * σ) * r_close := mul_lt_mul_of_pos_left hy_c (by positivity)
        _ ≤ (2 * σ) * (η_grad / (8 * σ)) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = η_grad / 4 := by field_simp [hσ.ne']; ring
        _ < η_grad / 2 := by linarith
    calc ‖p₁ - (2 * σ) • (y - yε)‖ ≤ ‖p₁‖ + ‖(2 * σ) • (y - yε)‖ := norm_sub_le _ _
      _ < η_grad / 2 + η_grad / 2 := add_lt_add h1 h2
      _ = η_grad := by ring
  have hg₂_diff : ‖g₂ - g₂'‖ < η_grad := by
    have hvec : g₂ - g₂' = p₂ - (2 * σ) • (z - zε) := by dsimp only [g₂]; abel
    rw [hvec]
    have hz_c : ‖z - zε‖ < r_close := by simpa [mem_ball, dist_eq_norm] using hyz_close.2
    have h1 : ‖p₂‖ < η_grad / 2 := lt_of_lt_of_le hp₂ (min_le_left _ _)
    have h2 : ‖(2 * σ) • (z - zε)‖ < η_grad / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * σ)]
      have hr : r_close ≤ η_grad / (8 * σ) := min_le_right _ _
      calc (2 * σ) * ‖z - zε‖ < (2 * σ) * r_close := mul_lt_mul_of_pos_left hz_c (by positivity)
        _ ≤ (2 * σ) * (η_grad / (8 * σ)) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = η_grad / 4 := by field_simp [hσ.ne']; ring
        _ < η_grad / 2 := by linarith
    calc ‖p₂ - (2 * σ) • (z - zε)‖ ≤ ‖p₂‖ + ‖(2 * σ) • (z - zε)‖ := norm_sub_le _ _
      _ < η_grad / 2 + η_grad / 2 := add_lt_add h1 h2
      _ = η_grad := by ring
  have hg₁'_ge : r_lo ≤ ‖g₁'‖ := by
    have h := norm_sub_norm_le g₁ g₁'
    have hη : η_grad ≤ r_lo / 2 := min_le_left _ _
    linarith
  have hg₂'_ge : r_lo ≤ ‖g₂'‖ := by
    have h := norm_sub_norm_le g₂ g₂'
    have hη : η_grad ≤ r_lo / 2 := min_le_left _ _
    linarith
  have hg₁'_ne : g₁' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr_lo hg₁'_ge)
  have hg₂'_ne : g₂' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hr_lo hg₂'_ge)
  -- Viscosity subsolution inequalities for uε at y and vε at z!
  have hy_Ωu : y ∈ Ωu := hsub_u (ball_subset_closedBall (ball_subset_ball (by linarith : ρ / 3 ≤ ρ) hy_ball))
  have hz_Ωv : z ∈ Ωv := hsub_v (ball_subset_closedBall (ball_subset_ball (by linarith : ρ / 3 ≤ ρ) hz_ball))
  have hvisc_u : 0 ≤ matrixNormalizedPLaplacian p g₁' A₁' :=
    htuε.matrixNormalizedPLaplacian_nonneg huε_visc hy_Ωu hg₁'_ne
  have hvisc_v : 0 ≤ matrixNormalizedPLaplacian p g₂' A₂' :=
    htvε.matrixNormalizedPLaplacian_nonneg hvε_visc hz_Ωv hg₂'_ne
  -- Apply taylor_envelope_normalizedPLaplacian_le!
  have hcontact := taylor_envelope_normalizedPLaplacian_le hp ht ht1 (rfl : x = t • y + (1 - t) • z)
    htu_pert htv_pert hg₁_ne hg₂_ne hφ_sh_at (by rw [hgrad_sh]; exact hgφ_ne)
    (by dsimp only [φ_sh, C_shift]; ring)
    (by dsimp only [φ_sh, C_shift, u_pert, v_pert]; rw [heq_pert]; ring)
    htouch_ev
  rw [hgrad_sh, hlap_sh, ha_eq, hb_eq] at hcontact
  -- Relate matrixNormalizedPLaplacian p g₁ A₁ to matrixNormalizedPLaplacian p g₁' A₁'
  have htr_id (g : Space n) (hg : g ≠ 0) :
      matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ (Space n)) = (n : ℝ) + p - 2 := by
    unfold matrixNormalizedPLaplacian
    have htr : LinearMap.trace ℝ (Space n) (ContinuousLinearMap.id ℝ (Space n)).toLinearMap = (n : ℝ) := by
      have : (ContinuousLinearMap.id ℝ (Space n)).toLinearMap = LinearMap.id := rfl
      rw [this, LinearMap.trace_id]
      simp [finrank_euclideanSpace_fin]
    rw [htr, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    have hgn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
    field_simp [hgn]; ring
  have hA₁_shift : matrixNormalizedPLaplacian p g₁ A₁ =
      matrixNormalizedPLaplacian p g₁ A₁' - 2 * σ * ((n : ℝ) + p - 2) := by
    have h : A₁ = A₁' + (-(2 * σ)) • ContinuousLinearMap.id ℝ (Space n) := by
      dsimp only [A₁]; ext v; simp [sub_eq_add_neg]
    rw [h, matrixNormalizedPLaplacian_add, matrixNormalizedPLaplacian_smul, htr_id g₁ hg₁_ne]
    ring
  have hA₂_shift : matrixNormalizedPLaplacian p g₂ A₂ =
      matrixNormalizedPLaplacian p g₂ A₂' - 2 * σ * ((n : ℝ) + p - 2) := by
    have h : A₂ = A₂' + (-(2 * σ)) • ContinuousLinearMap.id ℝ (Space n) := by
      dsimp only [A₂]; ext v; simp [sub_eq_add_neg]
    rw [h, matrixNormalizedPLaplacian_add, matrixNormalizedPLaplacian_smul, htr_id g₂ hg₂_ne]
    ring
  have hlip₁ : |matrixNormalizedPLaplacian p g₁ A₁' - matrixNormalizedPLaplacian p g₁' A₁'| ≤
      s₀ / (32 * W_max) := by
    have h1 := abs_matrixNormalizedPLaplacian_sub_le (p := p) hr_lo hK_hess.le
      (by linarith : r_lo ≤ ‖g₁‖) hg₁'_ge hA₁'_norm
    have h2 : 4 * |p - 2| * K_hess / r_lo ≤ Lip_g := by dsimp only [Lip_g]; linarith
    have h3 : η_grad ≤ s₀ / (32 * W_max * Lip_g) := min_le_right _ _
    calc |matrixNormalizedPLaplacian p g₁ A₁' - matrixNormalizedPLaplacian p g₁' A₁'|
        ≤ (4 * |p - 2| * K_hess / r_lo) * ‖g₁ - g₁'‖ := h1
      _ ≤ Lip_g * η_grad := mul_le_mul h2 hg₁_diff.le (norm_nonneg _) hLip_g.le
      _ ≤ Lip_g * (s₀ / (32 * W_max * Lip_g)) := mul_le_mul_of_nonneg_left h3 hLip_g.le
      _ = s₀ / (32 * W_max) := by field_simp [hLip_g.ne', hW_max.ne']
  have hlip₂ : |matrixNormalizedPLaplacian p g₂ A₂' - matrixNormalizedPLaplacian p g₂' A₂'| ≤
      s₀ / (32 * W_max) := by
    have h1 := abs_matrixNormalizedPLaplacian_sub_le (p := p) hr_lo hK_hess.le
      (by linarith : r_lo ≤ ‖g₂‖) hg₂'_ge hA₂'_norm
    have h2 : 4 * |p - 2| * K_hess / r_lo ≤ Lip_g := by dsimp only [Lip_g]; linarith
    have h3 : η_grad ≤ s₀ / (32 * W_max * Lip_g) := min_le_right _ _
    calc |matrixNormalizedPLaplacian p g₂ A₂' - matrixNormalizedPLaplacian p g₂' A₂'|
        ≤ (4 * |p - 2| * K_hess / r_lo) * ‖g₂ - g₂'‖ := h1
      _ ≤ Lip_g * η_grad := mul_le_mul h2 hg₂_diff.le (norm_nonneg _) hLip_g.le
      _ ≤ Lip_g * (s₀ / (32 * W_max * Lip_g)) := mul_le_mul_of_nonneg_left h3 hLip_g.le
      _ = s₀ / (32 * W_max) := by field_simp [hLip_g.ne', hW_max.ne']
  have hL₁_ge : -(s₀ / (32 * W_max)) - 2 * σ * ((n : ℝ) + p - 2) ≤ matrixNormalizedPLaplacian p g₁ A₁ := by
    rw [hA₁_shift]; linarith [(abs_le.mp hlip₁).1, hvisc_u]
  have hL₂_ge : -(s₀ / (32 * W_max)) - 2 * σ * ((n : ℝ) + p - 2) ≤ matrixNormalizedPLaplacian p g₂ A₂ := by
    rw [hA₂_shift]; linarith [(abs_le.mp hlip₂).1, hvisc_v]
  have hw₁_pos : 0 ≤ t * (‖gradient φt x‖ / a) ^ 3 := by positivity
  have hw₂_pos : 0 ≤ (1 - t) * (‖gradient φt x‖ / b) ^ 3 := by positivity
  have hterm₁ : -(s₀ / 32) - 2 * σ * ((n : ℝ) + p - 2) * t⁻¹ ^ 2 ≤
      t * (‖gradient φt x‖ / a) ^ 3 * matrixNormalizedPLaplacian p g₁ A₁ := by
    have h1 := mul_le_mul_of_nonneg_left hL₁_ge hw₁_pos
    have h2 : t * (‖gradient φt x‖ / a) ^ 3 * (s₀ / (32 * W_max)) ≤ s₀ / 32 := by
      have hwW : t * (‖gradient φt x‖ / a) ^ 3 ≤ W_max := hw₁_le.trans (le_max_left _ _)
      calc t * (‖gradient φt x‖ / a) ^ 3 * (s₀ / (32 * W_max))
          ≤ W_max * (s₀ / (32 * W_max)) := mul_le_mul_of_nonneg_right hwW (by positivity)
        _ = s₀ / 32 := by field_simp [hW_max.ne']
    have h3 : t * (‖gradient φt x‖ / a) ^ 3 * (2 * σ * ((n : ℝ) + p - 2)) ≤
        2 * σ * ((n : ℝ) + p - 2) * t⁻¹ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hw₁_le (by positivity : (0 : ℝ) ≤ 2 * σ * ((n : ℝ) + p - 2))
      linarith
    linarith
  have hterm₂ : -(s₀ / 32) - 2 * σ * ((n : ℝ) + p - 2) * (1 - t)⁻¹ ^ 2 ≤
      (1 - t) * (‖gradient φt x‖ / b) ^ 3 * matrixNormalizedPLaplacian p g₂ A₂ := by
    have h1 := mul_le_mul_of_nonneg_left hL₂_ge hw₂_pos
    have h2 : (1 - t) * (‖gradient φt x‖ / b) ^ 3 * (s₀ / (32 * W_max)) ≤ s₀ / 32 := by
      have hwW : (1 - t) * (‖gradient φt x‖ / b) ^ 3 ≤ W_max := hw₂_le.trans (le_max_right _ _)
      calc (1 - t) * (‖gradient φt x‖ / b) ^ 3 * (s₀ / (32 * W_max))
          ≤ W_max * (s₀ / (32 * W_max)) := mul_le_mul_of_nonneg_right hwW (by positivity)
        _ = s₀ / 32 := by field_simp [hW_max.ne']
    have h3 : (1 - t) * (‖gradient φt x‖ / b) ^ 3 * (2 * σ * ((n : ℝ) + p - 2)) ≤
        2 * σ * ((n : ℝ) + p - 2) * (1 - t)⁻¹ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hw₂_le (by positivity : (0 : ℝ) ≤ 2 * σ * ((n : ℝ) + p - 2))
      linarith
    linarith
  have hsum_σ : 2 * σ * ((n : ℝ) + p - 2) * t⁻¹ ^ 2 +
      2 * σ * ((n : ℝ) + p - 2) * (1 - t)⁻¹ ^ 2 ≤ s₀ / 16 := by
    have h1 : t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2 ≤ 1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2 := by linarith only
    calc 2 * σ * ((n : ℝ) + p - 2) * t⁻¹ ^ 2 + 2 * σ * ((n : ℝ) + p - 2) * (1 - t)⁻¹ ^ 2
        = 2 * σ * ((n : ℝ) + p - 2) * (t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) := by ring
      _ ≤ 2 * σ * ((n : ℝ) + p - 2) * (1 + t⁻¹ ^ 2 + (1 - t)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s₀ / 16 := hσ_eq
  linarith [hx_prop.2.2, hcontact, hterm₁, hterm₂, hsum_σ]

/-- **Unified nonlinear sup-min envelope viscosity theorem (Lemma 7.2)** for all
`1 < p < ∞` and `n ≥ 2`, assuming only continuity, viscosity `p`-subsolution
property on `{u < M₀}` and `{v < M₀}`, and compact localization of upper
levels of `u`. -/
theorem viscosity_supConvolution_of_subsolutions (hn : 2 ≤ n) {p t M₀ : ℝ}
    (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu_visc : IsViscosityPSubsolution p {y | u y < M₀} u)
    (hv_visc : IsViscosityPSubsolution p {z | v z < M₀} v)
    (hWc : Continuous (supConvolution t u v))
    (hle : ∀ y z, min (u y) (v z) ≤ supConvolution t u v (t • y + (1 - t) • z))
    (hopt : ∀ x, supConvolution t u v x < M₀ →
      ∃ y z, x = t • y + (1 - t) • z ∧ supConvolution t u v x = min (u y) (v z))
    (hcompact : ∀ x, supConvolution t u v x < M₀ →
      ∃ τ : ℝ, τ < supConvolution t u v x ∧ IsCompact {y | τ ≤ u y}) :
    IsViscosityPSubsolution p {x | supConvolution t u v x < M₀} (supConvolution t u v) := by
  classical
  have ht1_pos : 0 < 1 - t := sub_pos.mpr ht1
  have hopenW : IsOpen {x | supConvolution t u v x < M₀} := isOpen_lt hWc continuous_const
  refine ⟨hp, hopenW, hWc.continuousOn.upperSemicontinuousOn, ?_⟩
  intro x₀ hx₀ φ hφ_at hWφ hupper hgφ0
  let W := supConvolution t u v
  change W x₀ < M₀ at hx₀
  obtain ⟨y₀, z₀, hxyz0, hmin0⟩ := hopt x₀ hx₀
  -- Case 1: u y₀ < v z₀
  by_cases hlt1 : u y₀ < v z₀
  · have huy0 : u y₀ = W x₀ := by dsimp only [W]; rw [hmin0, min_eq_left hlt1.le]
    have hy0_mem : y₀ ∈ {y | u y < M₀} := by change u y₀ < M₀; rw [huy0]; exact hx₀
    let ψ : Space n → ℝ := fun y => φ (t • y + (1 - t) • z₀)
    have haff_cont : Continuous (fun y : Space n => t • y + (1 - t) • z₀) :=
      (continuous_id.const_smul t).add continuous_const
    have hψ_at : ContDiffAt ℝ 2 ψ y₀ := by
      have haff_c2 : ContDiffAt ℝ 2 (fun y : Space n => t • y + (1 - t) • z₀) y₀ :=
        ((contDiff_id.const_smul t).add contDiff_const).contDiffAt
      exact (by rw [← hxyz0]; exact hφ_at : ContDiffAt ℝ 2 φ (t • y₀ + (1 - t) • z₀)).comp y₀ haff_c2
    have hψ_eq : u y₀ = ψ y₀ := by dsimp only [ψ]; rw [← hxyz0, huy0]; exact hWφ
    have hψ_upper : ∀ᶠ y in 𝓝 y₀, u y ≤ ψ y := by
      have hu_lt : ∀ᶠ y in 𝓝 y₀, u y < v z₀ :=
        hu.continuousAt.eventually (eventually_lt_nhds hlt1)
      have hW_le : ∀ᶠ y in 𝓝 y₀, W (t • y + (1 - t) • z₀) ≤ φ (t • y + (1 - t) • z₀) :=
        haff_cont.continuousAt.eventually (by simpa [hxyz0] using hupper)
      filter_upwards [hu_lt, hW_le] with y hy1 hy2
      calc u y = min (u y) (v z₀) := (min_eq_left hy1.le).symm
        _ ≤ W (t • y + (1 - t) • z₀) := hle y z₀
        _ ≤ ψ y := hy2
    obtain ⟨hgrad_ψ, hlap_ψ⟩ := normalizedPLaplacian_comp_smul_add (p := p) ht ((1 - t) • z₀) y₀
      (by simpa [hxyz0] using hφ_at)
    have hgrad_ψ_ne : gradient ψ y₀ ≠ 0 := by
      rw [hgrad_ψ, ← hxyz0]; exact smul_ne_zero ht.ne' hgφ0
    have hnonneg := hu_visc.2.2.2 y₀ hy0_mem ψ hψ_at hψ_eq hψ_upper hgrad_ψ_ne
    rw [hlap_ψ, ← hxyz0] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos ht)
  -- Case 2: v z₀ < u y₀
  by_cases hlt2 : v z₀ < u y₀
  · have hvz0 : v z₀ = W x₀ := by dsimp only [W]; rw [hmin0, min_eq_right hlt2.le]
    have hz0_mem : z₀ ∈ {z | v z < M₀} := by change v z₀ < M₀; rw [hvz0]; exact hx₀
    let ψ : Space n → ℝ := fun z => φ ((1 - t) • z + t • y₀)
    have haff_eq : ∀ z, (1 - t) • z + t • y₀ = t • y₀ + (1 - t) • z := fun z => add_comm _ _
    have haff_cont : Continuous (fun z : Space n => (1 - t) • z + t • y₀) :=
      (continuous_id.const_smul (1 - t)).add continuous_const
    have hψ_at : ContDiffAt ℝ 2 ψ z₀ := by
      have haff_c2 : ContDiffAt ℝ 2 (fun z : Space n => (1 - t) • z + t • y₀) z₀ :=
        ((contDiff_id.const_smul (1 - t)).add contDiff_const).contDiffAt
      exact (by rw [haff_eq, ← hxyz0]; exact hφ_at :
        ContDiffAt ℝ 2 φ ((1 - t) • z₀ + t • y₀)).comp z₀ haff_c2
    have hψ_eq : v z₀ = ψ z₀ := by dsimp only [ψ]; rw [haff_eq, ← hxyz0, hvz0]; exact hWφ
    have hψ_upper : ∀ᶠ z in 𝓝 z₀, v z ≤ ψ z := by
      have hv_lt : ∀ᶠ z in 𝓝 z₀, v z < u y₀ :=
        hv.continuousAt.eventually (eventually_lt_nhds hlt2)
      have hW_le : ∀ᶠ z in 𝓝 z₀, W ((1 - t) • z + t • y₀) ≤ φ ((1 - t) • z + t • y₀) :=
        haff_cont.continuousAt.eventually (by simpa [haff_eq, hxyz0] using hupper)
      filter_upwards [hv_lt, hW_le] with z hz1 hz2
      calc v z = min (u y₀) (v z) := (min_eq_right hz1.le).symm
        _ ≤ W (t • y₀ + (1 - t) • z) := hle y₀ z
        _ = W ((1 - t) • z + t • y₀) := by rw [haff_eq]
        _ ≤ ψ z := hz2
    obtain ⟨hgrad_ψ, hlap_ψ⟩ := normalizedPLaplacian_comp_smul_add (p := p) ht1_pos (t • y₀) z₀
      (by simpa [haff_eq, hxyz0] using hφ_at)
    have hgrad_ψ_ne : gradient ψ z₀ ≠ 0 := by
      rw [hgrad_ψ, haff_eq, ← hxyz0]; exact smul_ne_zero ht1_pos.ne' hgφ0
    have hnonneg := hv_visc.2.2.2 z₀ hz0_mem ψ hψ_at hψ_eq hψ_upper hgrad_ψ_ne
    rw [hlap_ψ, haff_eq, ← hxyz0] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos ht1_pos)
  -- Case 3: u y₀ = v z₀ = W x₀ < M₀
  by_contra hbad
  push Not at hbad
  let s₀ : ℝ := -normalizedPLaplacian p φ x₀
  have hs₀ : 0 < s₀ := neg_pos.mpr hbad
  let M₁ : ℝ := (W x₀ + M₀) / 2
  have hW_lt_M₁ : W x₀ < M₁ := by dsimp only [M₁]; linarith
  have hM₁_lt_M₀ : M₁ < M₀ := by dsimp only [M₁]; linarith
  have hnp_pos : (0 : ℝ) < (n : ℝ) + p - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let γ : ℝ := s₀ / (8 * ((n : ℝ) + p - 2))
  have hγ : 0 < γ := div_pos hs₀ (by positivity)
  let φγ : Space n → ℝ := fun x => φ x + γ * ‖x - x₀‖ ^ 2
  have hφγ_at : ContDiffAt ℝ 2 φγ x₀ :=
    hφ_at.add (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffAt
  obtain ⟨hgrad_φγ0, hlap_φγ0⟩ := normalizedPLaplacian_add_quad_self p γ x₀ hφ_at hgφ0
  have hlap_φγ0_eq : normalizedPLaplacian p φγ x₀ = -(3 / 4 : ℝ) * s₀ := by
    rw [hlap_φγ0]
    have h2γ : 2 * γ * ((n : ℝ) + p - 2) = s₀ / 4 := by
      dsimp only [γ]; field_simp [hnp_pos.ne']; ring
    dsimp only [s₀] at h2γ ⊢; linarith
  obtain ⟨U₀, hU₀_mem, hφ_U₀⟩ := hφ_at.contDiffOn le_rfl (by simp)
  obtain ⟨U₁, hU₁_sub, hU₁_open, hx₀_U₁⟩ := _root_.mem_nhds_iff.mp hU₀_mem
  obtain ⟨U₂, hU₂_sub, hU₂_open, hx₀_U₂⟩ := _root_.mem_nhds_iff.mp hupper
  let U : Set (Space n) := U₁ ∩ U₂
  have hU_open : IsOpen U := hU₁_open.inter hU₂_open
  have hx₀_U : x₀ ∈ U := ⟨hx₀_U₁, hx₀_U₂⟩
  have hφγ_U : ContDiffOn ℝ 2 φγ U :=
    (hφ_U₀.mono (inter_subset_left.trans hU₁_sub)).add
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffOn
  have hgrad_φγ_ne0 : gradient φγ x₀ ≠ 0 := by rw [hgrad_φγ0]; exact hgφ0
  have hgrad_φγ_cont : ContinuousAt (gradient φγ) x₀ :=
    (toDual ℝ (Space n)).symm.continuous.continuousAt.comp
      ((hφγ_at.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hlap_φγ_cont : ContinuousAt (fun x => normalizedPLaplacian p φγ x) x₀ :=
    continuousAt_normalizedPLaplacian hU_open hφγ_U hx₀_U hgrad_φγ_ne0
  have hφγ0_val : φγ x₀ = W x₀ := by
    dsimp only [φγ, W]; rw [sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero, hWφ]
  have hev_r : ∀ᶠ x in 𝓝 x₀,
      x ∈ U ∧ gradient φγ x ≠ 0 ∧ normalizedPLaplacian p φγ x < -(5 / 8 : ℝ) * s₀ ∧
      φγ x < (W x₀ + M₁) / 2 := by
    filter_upwards [hU_open.mem_nhds hx₀_U,
      hgrad_φγ_cont.eventually (isOpen_ne.mem_nhds hgrad_φγ_ne0),
      hlap_φγ_cont.eventually (eventually_lt_nhds (by linarith : normalizedPLaplacian p φγ x₀ < -(5 / 8 : ℝ) * s₀)),
      hφγ_at.continuousAt.eventually (eventually_lt_nhds (by rw [hφγ0_val]; linarith : φγ x₀ < (W x₀ + M₁) / 2))]
      with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r₀, hr₀, hr₀_prop⟩ := Metric.eventually_nhds_iff.mp hev_r
  let r₁ : ℝ := r₀ / 2
  have hr₁ : 0 < r₁ := half_pos hr₀
  have hball_r₁ (x : Space n) (hx : x ∈ closedBall x₀ r₁) :
      x ∈ U ∧ gradient φγ x ≠ 0 ∧ normalizedPLaplacian p φγ x < -(5 / 8 : ℝ) * s₀ ∧
      φγ x < (W x₀ + M₁) / 2 :=
    hr₀_prop (lt_of_le_of_lt (mem_closedBall.mp hx) (half_lt_self hr₀))
  obtain ⟨τ, hτ_lt, hKτ_comp⟩ := hcompact x₀ hx₀
  obtain ⟨R₁, hR₁_sub⟩ := hKτ_comp.isBounded.subset_closedBall (0 : Space n)
  let R₀ : ℝ := max (max (max R₁ 1) (‖y₀‖ + 1)) (‖z₀‖ + 1)
  have hR₀_pos : 0 < R₀ := by positivity
  let R₂ : ℝ := max (R₀ + 1) ((‖x₀‖ + r₁ + t * R₀) / (1 - t) + 1)
  have hR₂_pos : 0 < R₂ := by
    have : 0 < R₀ + 1 := by positivity
    exact lt_of_lt_of_le this (le_max_left _ _)
  let R_big : ℝ := R₂ + 2
  have hR_big_pos : 0 < R_big := by positivity
  let K : Set (Space n) := closedBall (0 : Space n) R_big
  have hK_comp : IsCompact K := isCompact_closedBall 0 R_big
  have hK_ne : K.Nonempty := nonempty_closedBall.mpr hR_big_pos.le
  let P : Set (Space n × Space n) :=
    {q | q.1 ∈ closedBall (0 : Space n) R₂ ∧ q.2 ∈ closedBall (0 : Space n) R₂ ∧
      t • q.1 + (1 - t) • q.2 ∈ closedBall x₀ r₁}
  have hP_comp : IsCompact P := by
    have hP_eq : P = (closedBall (0 : Space n) R₂ ×ˢ closedBall (0 : Space n) R₂) ∩
        (fun q : Space n × Space n => t • q.1 + (1 - t) • q.2) ⁻¹' closedBall x₀ r₁ := by
      ext q; simp [P, and_assoc]
    have hlin_cont : Continuous (fun q : Space n × Space n => t • q.1 + (1 - t) • q.2) :=
      (continuous_fst.const_smul t).add (continuous_snd.const_smul (1 - t))
    rw [hP_eq]
    exact ((isCompact_closedBall (0 : Space n) R₂).prod (isCompact_closedBall (0 : Space n) R₂)).inter_right
      (isClosed_closedBall.preimage hlin_cont)
  have hy₀_ball : y₀ ∈ ball (0 : Space n) R₂ := by
    rw [mem_ball, dist_zero_right]
    have h1 : ‖y₀‖ < ‖y₀‖ + 1 := by linarith
    have h2 : ‖y₀‖ + 1 ≤ R₀ := le_trans (le_max_right _ _) (le_max_left _ _)
    have h3 : R₀ < R₀ + 1 := by linarith
    exact lt_of_lt_of_le (lt_trans h1 (lt_of_le_of_lt h2 h3)) (le_max_left _ _)
  have hz₀_ball : z₀ ∈ ball (0 : Space n) R₂ := by
    rw [mem_ball, dist_zero_right]
    have h1 : ‖z₀‖ < ‖z₀‖ + 1 := by linarith
    have h2 : ‖z₀‖ + 1 ≤ R₀ := le_max_right _ _
    have h3 : R₀ < R₀ + 1 := by linarith
    exact lt_of_lt_of_le (lt_trans h1 (lt_of_le_of_lt h2 h3)) (le_max_left _ _)
  have hq₀_P : (y₀, z₀) ∈ P :=
    ⟨ball_subset_closedBall hy₀_ball, ball_subset_closedBall hz₀_ball, by
      rw [← hxyz0]; exact mem_closedBall_self hr₁.le⟩
  have hP_le (q : Space n × Space n) (hq : q ∈ P) :
      min (u q.1) (v q.2) - φγ (t • q.1 + (1 - t) • q.2) ≤
        -γ * ‖(t • q.1 + (1 - t) • q.2) - x₀‖ ^ 2 := by
    have hxU := (hball_r₁ _ hq.2.2).1.2
    have hle1 : min (u q.1) (v q.2) ≤ W (t • q.1 + (1 - t) • q.2) := hle q.1 q.2
    have hle2 : W (t • q.1 + (1 - t) • q.2) ≤ φ (t • q.1 + (1 - t) • q.2) := hU₂_sub hxU
    dsimp only [φγ]; linarith
  have hφγ_gt : ∀ᶠ x in 𝓝 x₀, (τ + W x₀) / 2 < φγ x :=
    hφγ_at.continuousAt.eventually (eventually_gt_nhds (by rw [hφγ0_val]; linarith))
  obtain ⟨r₂', hr₂', hr₂'_prop⟩ := Metric.eventually_nhds_iff.mp hφγ_gt
  let r₂ : ℝ := min (r₁ / 2) (r₂' / 2)
  have hr₂ : 0 < r₂ := lt_min (half_pos hr₁) (half_pos hr₂')
  let gap₀ : ℝ := min (min (γ * r₂ ^ 2) ((W x₀ - τ) / 2)) ((M₁ - W x₀) / 2)
  have hgap₀ : 0 < gap₀ := lt_min (lt_min (by positivity) (by linarith)) (by linarith)
  have hbdry_gap (q : Space n × Space n) (hq : q ∈ P)
      (hbd : q.1 ∉ ball (0 : Space n) R₂ ∨ q.2 ∉ ball (0 : Space n) R₂ ∨
        t • q.1 + (1 - t) • q.2 ∉ ball x₀ r₂) :
      min (u q.1) (v q.2) - φγ (t • q.1 + (1 - t) • q.2) ≤ -gap₀ := by
    by_cases hx : t • q.1 + (1 - t) • q.2 ∈ ball x₀ r₂
    · have hu_lt_τ : u q.1 < τ := by
        by_contra hge; push Not at hge
        have hq1_R₁ : ‖q.1‖ ≤ R₁ := by
          have := hR₁_sub hge; simpa [mem_closedBall, dist_zero_right] using this
        have hq1_R₀ : ‖q.1‖ ≤ R₀ :=
          hq1_R₁.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
        have hq1_in : q.1 ∈ ball (0 : Space n) R₂ := by
          rw [mem_ball, dist_zero_right]
          exact lt_of_le_of_lt hq1_R₀ (lt_of_lt_of_le (by linarith : R₀ < R₀ + 1) (le_max_left _ _))
        have hq2_in : q.2 ∈ ball (0 : Space n) R₂ := by
          rw [mem_ball, dist_zero_right]
          have hdist : ‖(t • q.1 + (1 - t) • q.2) - x₀‖ ≤ r₁ := by
            simpa [mem_closedBall, dist_eq_norm] using hq.2.2
          have hnorm_x : ‖t • q.1 + (1 - t) • q.2‖ ≤ ‖x₀‖ + r₁ := by
            have := norm_add_le ((t • q.1 + (1 - t) • q.2) - x₀) x₀
            rw [sub_add_cancel] at this; linarith
          have h1tq2 : (1 - t) • q.2 = (t • q.1 + (1 - t) • q.2) - t • q.1 := by abel
          have hnorm_q2 : (1 - t) * ‖q.2‖ ≤ ‖x₀‖ + r₁ + t * R₀ := by
            calc (1 - t) * ‖q.2‖ = ‖(1 - t) • q.2‖ := by
                  rw [norm_smul, Real.norm_of_nonneg ht1_pos.le]
              _ = ‖(t • q.1 + (1 - t) • q.2) - t • q.1‖ := congrArg norm h1tq2
              _ ≤ ‖t • q.1 + (1 - t) • q.2‖ + ‖t • q.1‖ := norm_sub_le _ _
              _ = ‖t • q.1 + (1 - t) • q.2‖ + t * ‖q.1‖ := by
                  rw [norm_smul, Real.norm_of_nonneg ht.le]
              _ ≤ (‖x₀‖ + r₁) + t * R₀ := by gcongr
              _ = ‖x₀‖ + r₁ + t * R₀ := by ring
          have hq2_le : ‖q.2‖ ≤ (‖x₀‖ + r₁ + t * R₀) / (1 - t) :=
            (le_div_iff₀' ht1_pos).mpr hnorm_q2
          exact lt_of_le_of_lt hq2_le
            (lt_of_lt_of_le (by linarith : (‖x₀‖ + r₁ + t * R₀) / (1 - t) < (‖x₀‖ + r₁ + t * R₀) / (1 - t) + 1)
              (le_max_right _ _))
        rcases hbd with h1 | h2 | h3
        · exact h1 hq1_in
        · exact h2 hq2_in
        · exact h3 hx
      have hφ_big : (τ + W x₀) / 2 < φγ (t • q.1 + (1 - t) • q.2) :=
        hr₂'_prop (lt_of_lt_of_le (mem_ball.mp hx) ((min_le_right _ _).trans (half_lt_self hr₂').le))
      have hmin_le : min (u q.1) (v q.2) ≤ u q.1 := min_le_left _ _
      have hgap_le : gap₀ ≤ (W x₀ - τ) / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    · have hdist : r₂ ≤ ‖(t • q.1 + (1 - t) • q.2) - x₀‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hx; exact hx
      have hsq : r₂ ^ 2 ≤ ‖(t • q.1 + (1 - t) • q.2) - x₀‖ ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg ((t • q.1 + (1 - t) • q.2) - x₀)]) hdist
      have h1 := hP_le q hq
      have hgap_le : gap₀ ≤ γ * r₂ ^ 2 := (min_le_left _ _).trans (min_le_left _ _)
      have hmul : γ * r₂ ^ 2 ≤ γ * ‖(t • q.1 + (1 - t) • q.2) - x₀‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hγ.le
      linarith only [h1, hgap_le, hmul]
  -- Uniform continuity of u and v on K to guarantee sup-conv maximizers stay in {u < M₀}, {v < M₀}
  have huK_cont : ContinuousOn u K := hu.continuousOn
  have hvK_cont : ContinuousOn v K := hv.continuousOn
  obtain ⟨δu, hδu, hδu_uc⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK_comp.uniformContinuousOn_of_continuous huK_cont)
      ((M₀ - M₁) / 2) (by linarith)
  obtain ⟨δv, hδv, hδv_uc⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK_comp.uniformContinuousOn_of_continuous hvK_cont)
      ((M₀ - M₁) / 2) (by linarith)
  obtain ⟨Mu, hMu⟩ := hK_comp.exists_bound_of_continuousOn huK_cont
  obtain ⟨Mv, hMv⟩ := hK_comp.exists_bound_of_continuousOn hvK_cont
  let M_osc : ℝ := max (max Mu Mv) 0 + 1
  have hM_osc : 0 < M_osc := by positivity
  obtain ⟨ε₁, hε₁, hε₁_u⟩ :=
    supConv_uniform_close hK_comp hK_ne huK_cont (show 0 < gap₀ / 4 by positivity)
  obtain ⟨ε₂, hε₂, hε₂_v⟩ :=
    supConv_uniform_close hK_comp hK_ne hvK_cont (show 0 < gap₀ / 4 by positivity)
  let δ_step : ℝ := min 1 (min δu δv)
  have hδ_step : 0 < δ_step := lt_min zero_lt_one (lt_min hδu hδv)
  let ε : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) (δ_step ^ 2 / (8 * M_osc))
  have hε : 0 < ε := lt_min (lt_min (half_pos hε₁) (half_pos hε₂)) (by positivity)
  let uε : Space n → ℝ := supConv K ε u
  let vε : Space n → ℝ := supConv K ε v
  have huε_ge (y : Space n) (hy : y ∈ K) : u y ≤ uε y := self_le_supConv hK_comp huK_cont hy
  have hvε_ge (z : Space n) (hz : z ∈ K) : v z ≤ vε z := self_le_supConv hK_comp hvK_cont hz
  have huε_close (y : Space n) (hy : y ∈ K) : uε y ≤ u y + gap₀ / 4 :=
    (hε₁_u ε hε (lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hε₁)) y hy).2
  have hvε_close (z : Space n) (hz : z ∈ K) : vε z ≤ v z + gap₀ / 4 :=
    (hε₂_v ε hε (lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hε₂)) z hz).2
  let Lε : ℝ≥0 := ⟨R_big / ε, by positivity⟩
  have hfuε_conv : ConvexOn ℝ univ (fun y => uε y + (1 / (2 * ε)) * ‖y‖ ^ 2) :=
    supConv_semiconvex_convexOn hK_comp hK_ne huK_cont
  have hfuε_lip : LipschitzWith Lε (fun y => uε y + (1 / (2 * ε)) * ‖y‖ ^ 2) :=
    supConv_semiconvex_lipschitzWith hK_comp hK_ne hε hR_big_pos.le
      (fun _ hx => by simpa [K, mem_closedBall, dist_zero_right] using hx) huK_cont
  have hfvε_conv : ConvexOn ℝ univ (fun z => vε z + (1 / (2 * ε)) * ‖z‖ ^ 2) :=
    supConv_semiconvex_convexOn hK_comp hK_ne hvK_cont
  have hfvε_lip : LipschitzWith Lε (fun z => vε z + (1 / (2 * ε)) * ‖z‖ ^ 2) :=
    supConv_semiconvex_lipschitzWith hK_comp hK_ne hε hR_big_pos.le
      (fun _ hx => by simpa [K, mem_closedBall, dist_zero_right] using hx) hvK_cont
  have huε_cont : Continuous uε := by
    have heq : uε = fun y => (uε y + (1 / (2 * ε)) * ‖y‖ ^ 2) - (1 / (2 * ε)) * ‖y‖ ^ 2 := by
      funext y; ring
    rw [heq]
    exact hfuε_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hvε_cont : Continuous vε := by
    have heq : vε = fun z => (vε z + (1 / (2 * ε)) * ‖z‖ ^ 2) - (1 / (2 * ε)) * ‖z‖ ^ 2 := by
      funext z; ring
    rw [heq]
    exact hfvε_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  -- Open domains Ωu, Ωv where uε, vε are viscosity p-subsolutions
  let Ωu : Set (Space n) := ball (0 : Space n) (R₂ + 1) ∩ {y | uε y < M₁}
  let Ωv : Set (Space n) := ball (0 : Space n) (R₂ + 1) ∩ {z | vε z < M₁}
  have hΩu_open : IsOpen Ωu := isOpen_ball.inter (isOpen_lt huε_cont continuous_const)
  have hΩv_open : IsOpen Ωv := isOpen_ball.inter (isOpen_lt hvε_cont continuous_const)
  have huε_visc : IsViscosityPSubsolution p Ωu uε := by
    refine supConv_isViscosityPSubsolution hu_visc hΩu_open hK_comp hK_ne huK_cont hε ?_
    intro y hy y' hy'K hy'eq
    have hyK : y ∈ K := by
      rw [mem_closedBall, dist_zero_right]
      have : ‖y‖ < R₂ + 1 := by simpa [mem_ball, dist_zero_right] using hy.1
      dsimp only [R_big]; linarith
    have hnorm_sq : ‖y - y'‖ ^ 2 ≤ 2 * ε * (u y' - u y) := by
      have hge := huε_ge y hyK
      dsimp only [uε] at hge
      have : (1 / (2 * ε)) * ‖y - y'‖ ^ 2 ≤ u y' - u y := by linarith only [hge, hy'eq]
      calc ‖y - y'‖ ^ 2 = (2 * ε) * ((1 / (2 * ε)) * ‖y - y'‖ ^ 2) := by field_simp [hε.ne']
        _ ≤ (2 * ε) * (u y' - u y) := mul_le_mul_of_nonneg_left this (by positivity)
    have hosc : u y' - u y ≤ 2 * M_osc := by
      have h1 : |u y'| ≤ Mu := by simpa [Real.norm_eq_abs] using hMu y' hy'K
      have h2 : |u y| ≤ Mu := by simpa [Real.norm_eq_abs] using hMu y hyK
      have h3 : Mu ≤ M_osc := by dsimp only [M_osc]; linarith [le_max_left Mu Mv, le_max_left (max Mu Mv) (0 : ℝ)]
      linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]
    have hdist_lt : ‖y - y'‖ < δ_step := by
      have hε_le : ε ≤ δ_step ^ 2 / (8 * M_osc) := min_le_right _ _
      have hsq : ‖y - y'‖ ^ 2 ≤ δ_step ^ 2 / 2 := by
        calc ‖y - y'‖ ^ 2 ≤ 2 * ε * (2 * M_osc) :=
              hnorm_sq.trans (mul_le_mul_of_nonneg_left hosc (by positivity))
          _ ≤ 2 * (δ_step ^ 2 / (8 * M_osc)) * (2 * M_osc) := by gcongr
          _ = δ_step ^ 2 / 2 := by field_simp [hM_osc.ne']; ring
      nlinarith only [hsq, norm_nonneg (y - y'), hδ_step]
    have hy'_int : y' ∈ interior K := by
      apply interior_mono ball_subset_closedBall
      rw [isOpen_ball.interior_eq, mem_ball, dist_zero_right]
      have hy_lt : ‖y‖ < R₂ + 1 := by simpa [mem_ball, dist_zero_right] using hy.1
      have htri := norm_add_le (y' - y) y
      rw [sub_add_cancel, norm_sub_rev] at htri
      have h1 : δ_step ≤ 1 := min_le_left _ _
      dsimp only [R_big]; linarith
    have hy'_lt : u y' < M₀ := by
      have hd : dist y' y < δu := by
        rw [dist_comm, dist_eq_norm]
        exact lt_of_lt_of_le hdist_lt ((min_le_right _ _).trans (min_le_left _ _))
      have huc := hδu_uc y' hy'K y hyK hd
      rw [Real.dist_eq] at huc
      have huy : u y < M₁ := lt_of_le_of_lt (huε_ge y hyK) hy.2
      linarith [(abs_le.mp huc.le).2]
    exact ⟨hy'_int, hy'_lt⟩
  have hvε_visc : IsViscosityPSubsolution p Ωv vε := by
    refine supConv_isViscosityPSubsolution hv_visc hΩv_open hK_comp hK_ne hvK_cont hε ?_
    intro z hz z' hz'K hz'eq
    have hzK : z ∈ K := by
      rw [mem_closedBall, dist_zero_right]
      have : ‖z‖ < R₂ + 1 := by simpa [mem_ball, dist_zero_right] using hz.1
      dsimp only [R_big]; linarith
    have hnorm_sq : ‖z - z'‖ ^ 2 ≤ 2 * ε * (v z' - v z) := by
      have hge := hvε_ge z hzK
      dsimp only [vε] at hge
      have : (1 / (2 * ε)) * ‖z - z'‖ ^ 2 ≤ v z' - v z := by linarith only [hge, hz'eq]
      calc ‖z - z'‖ ^ 2 = (2 * ε) * ((1 / (2 * ε)) * ‖z - z'‖ ^ 2) := by field_simp [hε.ne']
        _ ≤ (2 * ε) * (v z' - v z) := mul_le_mul_of_nonneg_left this (by positivity)
    have hosc : v z' - v z ≤ 2 * M_osc := by
      have h1 : |v z'| ≤ Mv := by simpa [Real.norm_eq_abs] using hMv z' hz'K
      have h2 : |v z| ≤ Mv := by simpa [Real.norm_eq_abs] using hMv z hzK
      have h3 : Mv ≤ M_osc := by dsimp only [M_osc]; linarith [le_max_right Mu Mv, le_max_left (max Mu Mv) (0 : ℝ)]
      linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]
    have hdist_lt : ‖z - z'‖ < δ_step := by
      have hε_le : ε ≤ δ_step ^ 2 / (8 * M_osc) := min_le_right _ _
      have hsq : ‖z - z'‖ ^ 2 ≤ δ_step ^ 2 / 2 := by
        calc ‖z - z'‖ ^ 2 ≤ 2 * ε * (2 * M_osc) :=
              hnorm_sq.trans (mul_le_mul_of_nonneg_left hosc (by positivity))
          _ ≤ 2 * (δ_step ^ 2 / (8 * M_osc)) * (2 * M_osc) := by gcongr
          _ = δ_step ^ 2 / 2 := by field_simp [hM_osc.ne']; ring
      nlinarith only [hsq, norm_nonneg (z - z'), hδ_step]
    have hz'_int : z' ∈ interior K := by
      apply interior_mono ball_subset_closedBall
      rw [isOpen_ball.interior_eq, mem_ball, dist_zero_right]
      have hz_lt : ‖z‖ < R₂ + 1 := by simpa [mem_ball, dist_zero_right] using hz.1
      have htri := norm_add_le (z' - z) z
      rw [sub_add_cancel, norm_sub_rev] at htri
      have h1 : δ_step ≤ 1 := min_le_left _ _
      dsimp only [R_big]; linarith
    have hz'_lt : v z' < M₀ := by
      have hd : dist z' z < δv := by
        rw [dist_comm, dist_eq_norm]
        exact lt_of_lt_of_le hdist_lt ((min_le_right _ _).trans (min_le_right _ _))
      have hvc := hδv_uc z' hz'K z hzK hd
      rw [Real.dist_eq] at hvc
      have hvz : v z < M₁ := lt_of_le_of_lt (hvε_ge z hzK) hz.2
      linarith [(abs_le.mp hvc.le).2]
    exact ⟨hz'_int, hz'_lt⟩
  -- Maximize H_ε(y, z) = min(uε y, vε z) - φγ(t•y + (1-t)•z) on compact set P
  let Hε : Space n × Space n → ℝ := fun q => min (uε q.1) (vε q.2) - φγ (t • q.1 + (1 - t) • q.2)
  have hHε_cont : ContinuousOn Hε P := by
    have h1 : ContinuousOn (fun q : Space n × Space n => min (uε q.1) (vε q.2)) P :=
      ((huε_cont.comp continuous_fst).inf (hvε_cont.comp continuous_snd)).continuousOn
    have h2 : ContinuousOn (fun q : Space n × Space n => φγ (t • q.1 + (1 - t) • q.2)) P :=
      hφγ_U.continuousOn.comp
        ((continuous_fst.const_smul t).add (continuous_snd.const_smul (1 - t))).continuousOn
        (fun q hq => (hball_r₁ _ hq.2.2).1)
    exact h1.sub h2
  obtain ⟨qε, hqε_P, hqε_max⟩ := hP_comp.exists_isMaxOn ⟨(y₀, z₀), hq₀_P⟩ hHε_cont
  let yε : Space n := qε.1
  let zε : Space n := qε.2
  let xε : Space n := t • yε + (1 - t) • zε
  -- Hε(y₀, z₀) ≥ 0, so Hε(qε) ≥ 0, hence qε is STRICTLY INTERIOR to P!
  have hHε_ge0 : 0 ≤ Hε qε := by
    have h0 : 0 ≤ Hε (y₀, z₀) := by
      have hy₀K : y₀ ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) (ball_subset_closedBall hy₀_ball)
      have hz₀K : z₀ ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) (ball_subset_closedBall hz₀_ball)
      dsimp only [Hε]
      rw [← hxyz0, hφγ0_val]
      dsimp only [W]
      rw [hmin0]
      linarith only [min_le_min (huε_ge y₀ hy₀K) (hvε_ge z₀ hz₀K)]
    exact h0.trans (hqε_max hq₀_P)
  have hyε_int : yε ∈ ball (0 : Space n) R₂ ∧ zε ∈ ball (0 : Space n) R₂ ∧ xε ∈ ball x₀ r₂ := by
    by_contra hnot
    have hbd : yε ∉ ball (0 : Space n) R₂ ∨ zε ∉ ball (0 : Space n) R₂ ∨ xε ∉ ball x₀ r₂ := by
      tauto
    have hgap := hbdry_gap qε hqε_P hbd
    have hyεK : yε ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) hqε_P.1
    have hzεK : zε ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) hqε_P.2.1
    have hmin_cl : min (uε yε) (vε zε) ≤ min (u yε) (v zε) + gap₀ / 4 := by
      have h1 : uε yε ≤ u yε + gap₀ / 4 := huε_close yε hyεK
      have h2 : vε zε ≤ v zε + gap₀ / 4 := hvε_close zε hzεK
      exact (min_le_min h1 h2).trans_eq (min_add_add_right _ _ _)
    dsimp only [Hε, yε, zε, xε] at hHε_ge0 hmin_cl hgap
    linarith only [hHε_ge0, hmin_cl, hgap, hgap₀]
  -- Also min(uε yε, vε zε) < M₁!
  have hmin_lt_M₁ : min (uε yε) (vε zε) < M₁ := by
    have hyεK : yε ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) hqε_P.1
    have hzεK : zε ∈ K := closedBall_subset_closedBall (by dsimp only [R_big]; linarith only) hqε_P.2.1
    have hmin_cl : min (uε yε) (vε zε) ≤ min (u yε) (v zε) + gap₀ / 4 := by
      exact (min_le_min (huε_close yε hyεK) (hvε_close zε hzεK)).trans_eq (min_add_add_right _ _ _)
    have hle_φ : min (u yε) (v zε) ≤ φγ xε := by
      have hle_q := hP_le qε hqε_P
      have hnn : 0 ≤ γ * ‖xε - x₀‖ ^ 2 := by positivity
      dsimp only [yε, zε, xε] at hnn ⊢
      linarith only [hle_q, hnn]
    have hφ_lt := (hball_r₁ xε hqε_P.2.2).2.2.2
    have hgap_le : gap₀ ≤ (M₁ - W x₀) / 2 := min_le_right _ _
    linarith only [hmin_cl, hle_φ, hφ_lt, hgap_le, hW_lt_M₁]
  -- Find a small radius ρ₁ > 0 so closedBall yε ρ₁ × closedBall zε ρ₁ ⊆ P
  have hyε_open : ball (0 : Space n) R₂ ∈ 𝓝 yε := isOpen_ball.mem_nhds hyε_int.1
  have hzε_open : ball (0 : Space n) R₂ ∈ 𝓝 zε := isOpen_ball.mem_nhds hyε_int.2.1
  obtain ⟨r_a, hr_a, hr_a_prop⟩ := Metric.isOpen_iff.mp isOpen_ball yε hyε_int.1
  obtain ⟨r_b, hr_b, hr_b_prop⟩ := Metric.isOpen_iff.mp isOpen_ball zε hyε_int.2.1
  obtain ⟨r_c, hr_c, hr_c_prop⟩ := Metric.isOpen_iff.mp isOpen_ball xε hyε_int.2.2
  let ρ₁ : ℝ := min (min (r_a / 2) (r_b / 2)) (r_c / 4)
  have hρ₁ : 0 < ρ₁ := lt_min (lt_min (half_pos hr_a) (half_pos hr_b)) (by positivity)
  have hloc_max : ∀ y ∈ closedBall yε ρ₁, ∀ z ∈ closedBall zε ρ₁,
      min (uε y) (vε z) - φγ (t • y + (1 - t) • z) ≤
      min (uε yε) (vε zε) - φγ (t • yε + (1 - t) • zε) := by
    intro y hy z hz
    have hqP : (y, z) ∈ P := by
      refine ⟨?_, ?_, ?_⟩
      · apply ball_subset_closedBall; apply hr_a_prop
        exact lt_of_le_of_lt (mem_closedBall.mp hy)
          (((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hr_a))
      · apply ball_subset_closedBall; apply hr_b_prop
        exact lt_of_le_of_lt (mem_closedBall.mp hz)
          (((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hr_b))
      · apply ball_subset_closedBall
        apply ball_subset_ball (show r₂ ≤ r₁ by exact (min_le_left _ _).trans (half_lt_self hr₁).le)
        apply hr_c_prop
        dsimp only
        rw [mem_ball, dist_eq_norm]
        have hy' : ‖y - yε‖ ≤ ρ₁ := by simpa [mem_closedBall, dist_eq_norm] using hy
        have hz' : ‖z - zε‖ ≤ ρ₁ := by simpa [mem_closedBall, dist_eq_norm] using hz
        have hvec : (t • y + (1 - t) • z) - xε = t • (y - yε) + (1 - t) • (z - zε) := by
          dsimp only [xε]; module
        rw [hvec]
        calc ‖t • (y - yε) + (1 - t) • (z - zε)‖
            ≤ ‖t • (y - yε)‖ + ‖(1 - t) • (z - zε)‖ := norm_add_le _ _
          _ = t * ‖y - yε‖ + (1 - t) * ‖z - zε‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht1_pos.le]
          _ ≤ t * ρ₁ + (1 - t) * ρ₁ := by gcongr
          _ = ρ₁ := by ring
          _ ≤ r_c / 4 := min_le_right _ _
          _ < r_c := by linarith only [hr_c]
    have hm : Hε (y, z) ≤ Hε qε := hqε_max hqP
    dsimp only [Hε] at hm
    dsimp only [yε, zε]
    exact hm
  have hxε_prop := hball_r₁ xε hqε_P.2.2
  -- Case A: uε yε < vε zε (direct touch on uε!)
  by_cases hltA : uε yε < vε zε
  · have hyε_Ωu : yε ∈ Ωu :=
      ⟨ball_subset_ball (by linarith : R₂ ≤ R₂ + 1) hyε_int.1,
       by change uε yε < M₁; rw [← min_eq_left hltA.le]; exact hmin_lt_M₁⟩
    let C_s : ℝ := uε yε - φγ xε
    let ψ : Space n → ℝ := fun y => φγ (t • y + (1 - t) • zε) + C_s
    have hψ_at : ContDiffAt ℝ 2 ψ yε := by
      have haff : ContDiffAt ℝ 2 (fun y : Space n => t • y + (1 - t) • zε) yε :=
        ((contDiff_id.const_smul t).add contDiff_const).contDiffAt
      exact ((hφγ_U.contDiffAt (hU_open.mem_nhds hxε_prop.1)).comp yε haff).add contDiffAt_const
    have hψ_eq : uε yε = ψ yε := by dsimp only [ψ, C_s, xε]; ring
    have hψ_upper : ∀ᶠ y in 𝓝 yε, uε y ≤ ψ y := by
      have hu_lt : ∀ᶠ y in 𝓝 yε, uε y < vε zε :=
        huε_cont.continuousAt.eventually (eventually_lt_nhds hltA)
      have hcl : closedBall yε ρ₁ ∈ 𝓝 yε := Metric.closedBall_mem_nhds yε hρ₁
      filter_upwards [hu_lt, hcl] with y hy1 hy2
      have hm := hloc_max y hy2 zε (mem_closedBall_self hρ₁.le)
      rw [min_eq_left hy1.le, min_eq_left hltA.le] at hm
      dsimp only [ψ, C_s, xε]; linarith
    obtain ⟨hgrad_ψ, hlap_ψ⟩ := normalizedPLaplacian_comp_smul_add (p := p) ht ((1 - t) • zε) yε
      (hφγ_U.contDiffAt (hU_open.mem_nhds hxε_prop.1))
    have hgrad_ψ' : gradient ψ yε = t • gradient φγ xε := by
      dsimp only [ψ]; rw [BMCompactAnalytic.gradient_add_const, hgrad_ψ]
    have hlap_ψ' : normalizedPLaplacian p ψ yε = t ^ 2 * normalizedPLaplacian p φγ xε := by
      dsimp only [ψ]; rw [BMCompactAnalytic.normalizedPLaplacian_add_const, hlap_ψ]
    have hnonneg := huε_visc.2.2.2 yε hyε_Ωu ψ hψ_at hψ_eq hψ_upper
      (by rw [hgrad_ψ']; exact smul_ne_zero ht.ne' hxε_prop.2.1)
    rw [hlap_ψ'] at hnonneg
    have hge0 := nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos ht)
    linarith [hxε_prop.2.2.1]
  -- Case B: vε zε < uε yε (direct touch on vε!)
  by_cases hltB : vε zε < uε yε
  · have hzε_Ωv : zε ∈ Ωv :=
      ⟨ball_subset_ball (by linarith : R₂ ≤ R₂ + 1) hyε_int.2.1,
       by change vε zε < M₁; rw [← min_eq_right hltB.le]; exact hmin_lt_M₁⟩
    let C_s : ℝ := vε zε - φγ xε
    let ψ : Space n → ℝ := fun z => φγ ((1 - t) • z + t • yε) + C_s
    have haff_eq : ∀ z, (1 - t) • z + t • yε = t • yε + (1 - t) • z := fun z => add_comm _ _
    have hψ_at : ContDiffAt ℝ 2 ψ zε := by
      have haff : ContDiffAt ℝ 2 (fun z : Space n => (1 - t) • z + t • yε) zε :=
        ((contDiff_id.const_smul (1 - t)).add contDiff_const).contDiffAt
      have hφγ_at' : ContDiffAt ℝ 2 φγ ((1 - t) • zε + t • yε) := by
        rw [haff_eq]; exact hφγ_U.contDiffAt (hU_open.mem_nhds hxε_prop.1)
      exact (hφγ_at'.comp zε haff).add contDiffAt_const
    have hψ_eq : vε zε = ψ zε := by dsimp only [ψ, C_s]; rw [haff_eq]; dsimp only [xε]; ring
    have hψ_upper : ∀ᶠ z in 𝓝 zε, vε z ≤ ψ z := by
      have hv_lt : ∀ᶠ z in 𝓝 zε, vε z < uε yε :=
        hvε_cont.continuousAt.eventually (eventually_lt_nhds hltB)
      have hcl : closedBall zε ρ₁ ∈ 𝓝 zε := Metric.closedBall_mem_nhds zε hρ₁
      filter_upwards [hv_lt, hcl] with z hz1 hz2
      have hm := hloc_max yε (mem_closedBall_self hρ₁.le) z hz2
      rw [min_eq_right hz1.le, min_eq_right hltB.le] at hm
      dsimp only [ψ, C_s]; rw [haff_eq]; dsimp only [xε]; linarith
    obtain ⟨hgrad_ψ, hlap_ψ⟩ := normalizedPLaplacian_comp_smul_add (p := p) ht1_pos (t • yε) zε
      (by simpa [haff_eq, xε] using hφγ_U.contDiffAt (hU_open.mem_nhds hxε_prop.1))
    have hgrad_ψ' : gradient ψ zε = (1 - t) • gradient φγ xε := by
      dsimp only [ψ]; rw [BMCompactAnalytic.gradient_add_const, hgrad_ψ, haff_eq]
    have hlap_ψ' : normalizedPLaplacian p ψ zε = (1 - t) ^ 2 * normalizedPLaplacian p φγ xε := by
      dsimp only [ψ]; rw [BMCompactAnalytic.normalizedPLaplacian_add_const, hlap_ψ, haff_eq]
    have hnonneg := hvε_visc.2.2.2 zε hzε_Ωv ψ hψ_at hψ_eq hψ_upper
      (by rw [hgrad_ψ']; exact smul_ne_zero ht1_pos.ne' hxε_prop.2.1)
    rw [hlap_ψ'] at hnonneg
    have hge0 := nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos ht1_pos)
    linarith [hxε_prop.2.2.1]
  -- Case C: uε yε = vε zε < M₁ — apply envelope_semiconvex_contradiction!
  have heq_ε : uε yε = vε zε := le_antisymm (not_lt.mp hltB) (not_lt.mp hltA)
  have hyε_Ωu : yε ∈ Ωu :=
    ⟨ball_subset_ball (by linarith : R₂ ≤ R₂ + 1) hyε_int.1,
     by change uε yε < M₁; rwa [heq_ε, min_self, ← heq_ε] at hmin_lt_M₁⟩
  have hzε_Ωv : zε ∈ Ωv :=
    ⟨ball_subset_ball (by linarith : R₂ ≤ R₂ + 1) hyε_int.2.1,
     by change vε zε < M₁; rwa [heq_ε, min_self] at hmin_lt_M₁⟩
  exact envelope_semiconvex_contradiction hn hp ht ht1 hε hs₀
    hfuε_conv hfuε_lip hfvε_conv hfvε_lip hΩu_open hΩv_open hU_open
    huε_visc hvε_visc hφγ_U hyε_Ωu hzε_Ωv hxε_prop.1 hxε_prop.2.1 hxε_prop.2.2.1
    heq_ε hρ₁ hloc_max

/-- **General Lemma 7.2 (subcritical / unit-potential regime)**:
for all `1 < p < ∞` and `n ≥ 2`, the supremal convolution of two continuous
positive decaying weak `p`-harmonic functions on `{u < 1}` and `{v < 1}` is a
viscosity `p`-subsolution on `{supConvolution t u v < 1}` — with NO `C¹` or `C²`
regularity hypothesis. -/
theorem weak_viscosity_supConvolution_subcritical_allp {n : ℕ} (hn : 2 ≤ n)
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu_pos : ∀ x, 0 < u x) (hv_pos : ∀ x, 0 < v x)
    (hu_decay : Tendsto u (Bornology.cobounded (Space n)) (𝓝 0))
    (hu_le : ∀ x, u x ≤ 1)
    (hu_harm : IsWeakPHarmonic p {y | u y < 1} u)
    (hv_harm : IsWeakPHarmonic p {z | v z < 1} v) :
    IsViscosityPSubsolution p {x | supConvolution t u v x < 1} (supConvolution t u v) := by
  have htne : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
  refine viscosity_supConvolution_of_subsolutions hn hp ht ht1 hu hv
    (hu_harm.viscosity_of_continuous hu.continuousOn hn)
    (hv_harm.viscosity_of_continuous hv.continuousOn hn)
    (continuous_supConvolution_subcritical t htne hu hv hu_pos hv_pos hu_decay)
    (fun y z => min_le_supConvolution_of_decomposition t (v := v) hu_le rfl)
    (fun x _ => exists_optimalPair_subcritical t htne hu hv hu_pos hv_pos hu_decay x)
    (fun x _ => ?_)
  have hpos : 0 < supConvolution t u v x := by
    have h1 : 0 < min (u x) (v x) := lt_min (hu_pos x) (hv_pos x)
    have h2 : min (u x) (v x) ≤ supConvolution t u v x :=
      min_le_supConvolution_of_decomposition t (v := v) hu_le (by rw [← add_smul]; simp)
    exact lt_of_lt_of_le h1 h2
  exact ⟨supConvolution t u v x / 2, half_lt_self hpos,
    isCompact_superlevel_of_tendsto_zero hu hu_decay (half_pos hpos)⟩

/-- **General Lemma 7.2 (critical / supercritical exterior Green regime)**:
for all `1 < p < ∞` and `n ≥ 2`, the supremal convolution of two continuous
nonpositive weak `p`-harmonic functions on `{u < 0}` and `{v < 0}` with
`u → -∞` at infinity is a viscosity `p`-subsolution on `{supConvolution t u v < 0}`
— with NO `C¹` or `C²` regularity hypothesis. -/
theorem weak_viscosity_supConvolution_atBot_allp {n : ℕ} (hn : 2 ≤ n)
    {p t : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu_bot : Tendsto u (Bornology.cobounded (Space n)) atBot)
    (hu_le : ∀ x, u x ≤ 0)
    (hu_harm : IsWeakPHarmonic p {y | u y < 0} u)
    (hv_harm : IsWeakPHarmonic p {z | v z < 0} v) :
    IsViscosityPSubsolution p {x | supConvolution t u v x < 0} (supConvolution t u v) := by
  have htne : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
  refine viscosity_supConvolution_of_subsolutions hn hp ht ht1 hu hv
    (hu_harm.viscosity_of_continuous hu.continuousOn hn)
    (hv_harm.viscosity_of_continuous hv.continuousOn hn)
    (continuous_supConvolution_atBot t htne hu hv hu_bot)
    (fun y z => min_le_supConvolution_of_decomposition t (v := v) hu_le rfl)
    (fun x _ => exists_optimalPair_atBot t htne hu hv hu_bot x)
    (fun x _ => ?_)
  exact ⟨supConvolution t u v x - 1, by linarith,
    isCompact_superlevel_of_tendsto_atBot hu hu_bot (supConvolution t u v x - 1)⟩

end MainEnvelope
end BMCompactPDE
#print axioms BMCompactPDE.viscosity_supConvolution_of_subsolutions
#print axioms BMCompactPDE.weak_viscosity_supConvolution_subcritical_allp
#print axioms BMCompactPDE.weak_viscosity_supConvolution_atBot_allp
