import TaylorEnvelopeContact
import AlexandrovConvex
import Mathlib.Analysis.Calculus.MeanValue

/-! The `(2n + 1)`-dimensional perturbation lemma for the sup-min envelope
of two semiconvex functions against a noncritical `C²` test function `φ`.
Proves a uniform quadratic upper bound on the contact set (giving uniform
Lipschitzness of the subgradient map `(y, z, α) ↦ (p₁, p₂, c)` and uniform
Hessian upper bounds), and extracts perturbed maximizers in any full-measure
product set `A₁ × A₂` (in particular, the Alexandrov set). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal NNReal
namespace BMCompactPDE

section EnvelopePerturbation
variable {n : ℕ}

/-- Linear equivalence `((Space n × Space n) × ℝ) ≃L[ℝ] WithLp 2 (WithLp 2 (Space n × Space n) × ℝ)`. -/
def tripleLpEquiv (n : ℕ) :
    ((Space n × Space n) × ℝ) ≃L[ℝ] WithLp 2 (WithLp 2 (Space n × Space n) × ℝ) :=
  (((WithLp.linearEquiv 2 ℝ (Space n × Space n)).symm.prodCongr (LinearEquiv.refl ℝ ℝ)).trans
    (WithLp.linearEquiv 2 ℝ (WithLp 2 (Space n × Space n) × ℝ)).symm).toContinuousLinearEquiv

/-- On a closed ball inside an open `C²` domain, `φ` has a Lipschitz gradient
and satisfies a uniform quadratic upper bound. -/
theorem c2_quadratic_upper_bound {φ : Space n → ℝ} {U : Set (Space n)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) {x₀ : Space n} {R : ℝ} (hR : 0 < R)
    (hsub : closedBall x₀ R ⊆ U) :
    ∃ Cφ : ℝ, 0 < Cφ ∧
      LipschitzOnWith (Real.toNNReal Cφ) (gradient φ) (closedBall x₀ R) ∧
      ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
        φ y ≤ φ x + inner ℝ (gradient φ x) (y - x) + Cφ * ‖y - x‖ ^ 2 := by
  have hcomp : IsCompact (closedBall x₀ R) := isCompact_closedBall x₀ R
  have hne : (closedBall x₀ R).Nonempty := nonempty_closedBall.mpr hR.le
  have hgrad_c1 : ContDiffOn ℝ 1 (gradient φ) U := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ φ) U := by
      have h1 := hφ.fderiv_of_isOpen hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
      exact h1
    exact (toDual ℝ (Space n)).symm.toContinuousLinearMap.contDiff.comp_contDiffOn hfd
  have hfd_grad_cont : ContinuousOn (fun x => fderiv ℝ (gradient φ) x) (closedBall x₀ R) :=
    ((hgrad_c1.fderiv_of_isOpen hU (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn).mono hsub
  obtain ⟨x₁, -, hx₁⟩ := hcomp.exists_isMaxOn hne hfd_grad_cont.norm
  let Cφ : ℝ := ‖fderiv ℝ (gradient φ) x₁‖ + 1
  have hCφ : 0 < Cφ := by positivity
  have hgrad_lip : LipschitzOnWith (Real.toNNReal Cφ) (gradient φ) (closedBall x₀ R) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => (hgrad_c1.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num))
    · intro x hx
      have hle : ‖fderiv ℝ (gradient φ) x‖ ≤ ‖fderiv ℝ (gradient φ) x₁‖ := hx₁ hx
      change ‖fderiv ℝ (gradient φ) x‖ ≤ (Real.toNNReal Cφ : ℝ)
      rw [Real.coe_toNNReal Cφ hCφ.le]
      dsimp only [Cφ]; linarith
    · exact convex_closedBall x₀ R
  refine ⟨Cφ, hCφ, hgrad_lip, fun x hx y hy => ?_⟩
  let g : ℝ → ℝ := fun s => φ (x + s • (y - x)) - s * inner ℝ (gradient φ x) (y - x)
  have hg_deriv : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (inner ℝ (gradient φ (x + s • (y - x)) - gradient φ x) (y - x)) s := by
    intro s hs
    have hpt : x + s • (y - x) ∈ closedBall x₀ R := by
      have heq : x + s • (y - x) = (1 - s) • x + s • y := by module
      rw [heq]
      exact (convex_closedBall x₀ R) hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring)
    have hφd : HasFDerivAt φ (toDual ℝ (Space n) (gradient φ (x + s • (y - x)))) (x + s • (y - x)) :=
      ((hφ.contDiffAt (hU.mem_nhds (hsub hpt))).differentiableAt (by norm_num)).hasGradientAt.hasFDerivAt
    have hline : HasDerivAt (fun r : ℝ => x + r • (y - x)) (y - x) s := by
      simpa using ((hasDerivAt_id s).smul_const (y - x)).const_add x
    have h1 : HasDerivAt (fun r : ℝ => φ (x + r • (y - x)))
        (inner ℝ (gradient φ (x + s • (y - x))) (y - x)) s := by
      have h := hφd.comp_hasDerivAt s hline
      rwa [toDual_apply_apply] at h
    have h2 : HasDerivAt (fun r : ℝ => r * inner ℝ (gradient φ x) (y - x))
        (inner ℝ (gradient φ x) (y - x)) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (gradient φ x) (y - x))
    rw [inner_sub_left]
    exact h1.sub h2
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖inner ℝ (gradient φ (x + s • (y - x)) - gradient φ x) (y - x)‖ ≤ Cφ * ‖y - x‖ ^ 2 := by
    intro s hs
    have hpt : x + s • (y - x) ∈ closedBall x₀ R := by
      have heq : x + s • (y - x) = (1 - s) • x + s • y := by module
      rw [heq]
      exact (convex_closedBall x₀ R) hx hy (sub_nonneg.mpr hs.2) hs.1 (by ring)
    rw [Real.norm_eq_abs]
    have hlip := hgrad_lip.dist_le_mul (x + s • (y - x)) hpt x hx
    rw [Real.coe_toNNReal Cφ hCφ.le] at hlip
    change dist (gradient φ (x + s • (y - x))) (gradient φ x) ≤ Cφ * dist (x + s • (y - x)) x at hlip
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1] at hlip
    calc |inner ℝ (gradient φ (x + s • (y - x)) - gradient φ x) (y - x)|
        ≤ ‖gradient φ (x + s • (y - x)) - gradient φ x‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cφ * (s * ‖y - x‖)) * ‖y - x‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ ≤ (Cφ * (1 * ‖y - x‖)) * ‖y - x‖ := by gcongr; exact hs.2
      _ = Cφ * ‖y - x‖ ^ 2 := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun s => inner ℝ (gradient φ (x + s • (y - x)) - gradient φ x) (y - x))
    (fun s hs => (hg_deriv s hs).hasDerivWithinAt)
    hbound
    (convex_Icc 0 1) (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have h1 : ‖g 1 - g 0‖ ≤ Cφ * ‖y - x‖ ^ 2 * ‖(1 : ℝ) - 0‖ := hmvt
  simp only [g, one_smul, add_sub_cancel, one_mul, zero_smul, add_zero, zero_mul, sub_zero,
    Real.norm_eq_abs, abs_one, mul_one] at h1
  linarith [(abs_le.mp h1).2]

/-! ### Private modular helpers for `envelope_jensen_exists_good_maximizer` -/

private abbrev Q (n : ℕ) := WithLp 2 (WithLp 2 (Space n × Space n) × ℝ)

private abbrev qY (q : Q n) : Space n := (WithLp.ofLp (WithLp.ofLp q).1).1
private abbrev qZ (q : Q n) : Space n := (WithLp.ofLp (WithLp.ofLp q).1).2
private abbrev qA (q : Q n) : ℝ := (WithLp.ofLp q).2

private lemma hnorm_sq_Q (q : Q n) : ‖q‖ ^ 2 = ‖qY q‖ ^ 2 + ‖qZ q‖ ^ 2 + ‖qA q‖ ^ 2 := by
  have h1 : ‖q‖ ^ 2 = ‖(WithLp.ofLp q).1‖ ^ 2 + ‖qA q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      show inner ℝ q q = inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).1 +
        inner ℝ (qA q) (qA q) from rfl,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h2 : ‖(WithLp.ofLp q).1‖ ^ 2 = ‖qY q‖ ^ 2 + ‖qZ q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      show inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).1 = inner ℝ (qY q) (qY q) +
        inner ℝ (qZ q) (qZ q) from rfl,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  linarith only [h1, h2]

private lemma hqY_le (q : Q n) : ‖qY q‖ ≤ ‖q‖ := by
  have hsq : ‖qY q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    linarith only [hnorm_sq_Q q, sq_nonneg ‖qZ q‖, sq_nonneg ‖qA q‖]
  have habs : |‖qY q‖| ≤ |‖q‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

private lemma hqZ_le (q : Q n) : ‖qZ q‖ ≤ ‖q‖ := by
  have hsq : ‖qZ q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    linarith only [hnorm_sq_Q q, sq_nonneg ‖qY q‖, sq_nonneg ‖qA q‖]
  have habs : |‖qZ q‖| ≤ |‖q‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

private lemma hqA_le (q : Q n) : ‖qA q‖ ≤ ‖q‖ := by
  have hsq : ‖qA q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    linarith only [hnorm_sq_Q q, sq_nonneg ‖qY q‖, sq_nonneg ‖qZ q‖]
  have habs : |‖qA q‖| ≤ |‖q‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

private lemma hqY_lip : LipschitzWith 1 (qY (n := n)) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, show dist a b = ‖a - b‖ from dist_eq_norm a b]
    exact hqY_le (a - b)

private lemma hqZ_lip : LipschitzWith 1 (qZ (n := n)) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, show dist a b = ‖a - b‖ from dist_eq_norm a b]
    exact hqZ_le (a - b)

private lemma hqA_lip : LipschitzWith 1 (qA (n := n)) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, show dist a b = ‖a - b‖ from dist_eq_norm a b]
    exact hqA_le (a - b)

private lemma comb_mem_closedBall {t r : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {y₀ z₀ y z : Space n} (hy : y ∈ closedBall y₀ r) (hz : z ∈ closedBall z₀ r) :
    t • y + (1 - t) • z ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) := by
  rw [mem_closedBall, dist_eq_norm] at hy hz ⊢
  have hvec : (t • y + (1 - t) • z) - (t • y₀ + (1 - t) • z₀) =
      t • (y - y₀) + (1 - t) • (z - z₀) := by module
  rw [hvec]
  have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
  calc ‖t • (y - y₀) + (1 - t) • (z - z₀)‖
      ≤ ‖t • (y - y₀)‖ + ‖(1 - t) • (z - z₀)‖ := norm_add_le _ _
    _ = t * ‖y - y₀‖ + (1 - t) * ‖z - z₀‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg h1mt]
    _ ≤ t * r + (1 - t) * r :=
        add_le_add (mul_le_mul_of_nonneg_left hy ht.le) (mul_le_mul_of_nonneg_left hz h1mt)
    _ ≤ 2 * r := by
        have hr0 : 0 ≤ r := (norm_nonneg (y - y₀)).trans hy
        linarith only [hr0]

/-- Any globally `L`-Lipschitz function with a uniform quadratic upper bound on `closedBall y ρ₀`
for all `y ∈ S` has a Lipschitz subgradient map on `S`. -/
private theorem subgradient_lipschitzOn_of_quadratic_upper_bound
    {L : ℝ≥0} {ρ₀ C_upper : ℝ} (hρ₀ : 0 < ρ₀) (hC_upper : 0 < C_upper)
    {f : Space n → ℝ} (hf_lip : LipschitzWith L f)
    {S : Set (Space n)} {q : Space n → Space n}
    (hsub : ∀ y ∈ S, IsSubgradient f y (q y))
    (hup : ∀ y ∈ S, ∀ y' ∈ closedBall y ρ₀,
      f y' - f y ≤ inner ℝ (q y) (y' - y) + C_upper * ‖y' - y‖ ^ 2) :
    ∃ Lq : ℝ≥0, LipschitzOnWith Lq q S := by
  let Cq : ℝ := max (4 * C_upper) (4 * (L : ℝ) / ρ₀)
  have hCq_nn : 0 ≤ Cq :=
    le_trans (mul_nonneg (by norm_num) hC_upper.le) (le_max_left _ _)
  refine ⟨⟨Cq, hCq_nn⟩, LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ => ?_⟩
  change dist (q y₁) (q y₂) ≤ Cq * dist y₁ y₂
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hclose : ‖y₂ - y₁‖ ≤ ρ₀ / 2
  · by_cases hu : q y₂ - q y₁ = 0
    · rw [norm_sub_rev, hu, norm_zero]
      exact mul_nonneg hCq_nn (norm_nonneg _)
    · have hu_pos : 0 < ‖q y₂ - q y₁‖ := norm_pos_iff.mpr hu
      let v : Space n := (‖y₂ - y₁‖ / ‖q y₂ - q y₁‖) • (q y₂ - q y₁)
      have hv_norm : ‖v‖ = ‖y₂ - y₁‖ := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) hu_pos.le),
          div_mul_cancel₀ _ hu_pos.ne']
      have hyv_mem : y₂ + v ∈ closedBall y₁ ρ₀ := by
        rw [mem_closedBall, dist_eq_norm, show y₂ + v - y₁ = (y₂ - y₁) + v by abel]
        calc ‖(y₂ - y₁) + v‖ ≤ ‖y₂ - y₁‖ + ‖v‖ := norm_add_le _ _
          _ = 2 * ‖y₂ - y₁‖ := by rw [hv_norm]; ring
          _ ≤ ρ₀ := by linarith only [hclose]
      have h1 := hsub y₁ hy₁ y₂
      have h2 := hsub y₂ hy₂ (y₂ + v); rw [add_sub_cancel_left] at h2
      have h3 := hup y₁ hy₁ (y₂ + v) hyv_mem
      rw [show y₂ + v - y₁ = (y₂ - y₁) + v by abel, inner_add_right] at h3
      have hinner : inner ℝ (q y₂ - q y₁) v ≤ C_upper * ‖(y₂ - y₁) + v‖ ^ 2 := by
        rw [inner_sub_left]; linarith only [h1, h2, h3]
      have hlhs : inner ℝ (q y₂ - q y₁) v = ‖y₂ - y₁‖ * ‖q y₂ - q y₁‖ := by
        dsimp only [v]
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hu_pos.ne']
      have hrhs : ‖(y₂ - y₁) + v‖ ≤ 2 * ‖y₂ - y₁‖ := by
        calc ‖(y₂ - y₁) + v‖ ≤ ‖y₂ - y₁‖ + ‖v‖ := norm_add_le _ _
          _ = 2 * ‖y₂ - y₁‖ := by rw [hv_norm]; ring
      have hsq : ‖y₂ - y₁‖ * ‖q y₂ - q y₁‖ ≤ (4 * C_upper) * ‖y₂ - y₁‖ ^ 2 := by
        rw [← hlhs]
        calc inner ℝ (q y₂ - q y₁) v ≤ C_upper * ‖(y₂ - y₁) + v‖ ^ 2 := hinner
          _ ≤ C_upper * (2 * ‖y₂ - y₁‖) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hrhs 2) hC_upper.le
          _ = (4 * C_upper) * ‖y₂ - y₁‖ ^ 2 := by ring
      by_cases h0 : ‖y₂ - y₁‖ = 0
      · have heq : y₂ = y₁ := sub_eq_zero.mp (norm_eq_zero.mp h0)
        subst heq; simp at hu
      · have hpos : 0 < ‖y₂ - y₁‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        rw [norm_sub_rev y₁ y₂, norm_sub_rev (q y₁) (q y₂)]
        have hsq' : ‖y₂ - y₁‖ * ‖q y₂ - q y₁‖ ≤ ‖y₂ - y₁‖ * (4 * C_upper * ‖y₂ - y₁‖) := by
          linarith only [hsq,
            show (4 * C_upper) * ‖y₂ - y₁‖ ^ 2 = ‖y₂ - y₁‖ * (4 * C_upper * ‖y₂ - y₁‖) by ring]
        have h4 : ‖q y₂ - q y₁‖ ≤ 4 * C_upper * ‖y₂ - y₁‖ := le_of_mul_le_mul_left hsq' hpos
        exact h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have hgt : ρ₀ / 2 < ‖y₂ - y₁‖ := lt_of_not_ge hclose
    have h1 : ‖q y₁‖ ≤ (L : ℝ) := (hsub y₁ hy₁).norm_le hf_lip
    have h2 : ‖q y₂‖ ≤ (L : ℝ) := (hsub y₂ hy₂).norm_le hf_lip
    rw [norm_sub_rev y₁ y₂]
    calc ‖q y₁ - q y₂‖ ≤ ‖q y₁‖ + ‖q y₂‖ := norm_sub_le _ _
      _ ≤ 2 * (L : ℝ) := by linarith only [h1, h2]
      _ = (4 * (L : ℝ) / ρ₀) * (ρ₀ / 2) := by field_simp [hρ₀.ne']; ring
      _ ≤ (4 * (L : ℝ) / ρ₀) * ‖y₂ - y₁‖ :=
          mul_le_mul_of_nonneg_left hgt.le
            (div_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg L)) hρ₀.le)
      _ ≤ Cq * ‖y₂ - y₁‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- First-order subgradient alignment at an interior equal-value maximizer `(y, z)`:
any pair of subgradients `(q₁, q₂)` of `f₁, f₂` aligns with `∇φ(t•y + (1-t)•z)` with
weight `α ∈ [α₀, 1 - β₀]`. -/
private theorem envelope_first_order_subgradient_alignment
    {t M : ℝ} (ht : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    {L : ℝ≥0} {u₁ v₁ φ : Space n → ℝ}
    (hf₁_lip : LipschitzWith L (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2))
    (hf₂_lip : LipschitzWith L (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2))
    {y₀ z₀ : Space n} {r : ℝ} (hr : 0 < r)
    {U : Set (Space n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hsub : closedBall (t • y₀ + (1 - t) • z₀) (2 * r) ⊆ U)
    (hgrad_ne : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), gradient φ x ≠ 0)
    {d_min R_box C_max α₀ β₀ : ℝ} (hC_max : 0 < C_max)
    (hC_max_ge : (L : ℝ) + M * R_box + 1 ≤ C_max)
    (hα₀_le : α₀ ≤ t * d_min / C_max)
    (hβ₀_le : β₀ ≤ (1 - t) * d_min / C_max)
    (hd_ge : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), d_min ≤ ‖gradient φ x‖)
    {y z p₁ p₂ q₁ q₂ : Space n} {c : ℝ}
    (hy_in : y ∈ ball y₀ (r / 3)) (hz_in : z ∈ ball z₀ (r / 3))
    (hy_norm : ‖y‖ ≤ R_box) (hz_norm : ‖z‖ ≤ R_box)
    (hp₁_le : ‖p₁‖ ≤ 1) (hp₂_le : ‖p₂‖ ≤ 1)
    (heq_val : u₁ y + inner ℝ p₁ y = v₁ z + inner ℝ p₂ z + c)
    (hmax : ∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
      min (u₁ y' + inner ℝ p₁ y') (v₁ z' + inner ℝ p₂ z' + c) - φ (t • y' + (1 - t) • z') ≤
      min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) - φ (t • y + (1 - t) • z))
    (hq₁ : IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y q₁)
    (hq₂ : IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z q₂) :
    ∃ α : ℝ, α₀ ≤ α ∧ α ≤ 1 - β₀ ∧
      q₁ - M • y + p₁ = (t / α) • gradient φ (t • y + (1 - t) • z) ∧
      q₂ - M • z + p₂ = ((1 - t) / (1 - α)) • gradient φ (t • y + (1 - t) • z) := by
  have ht_pos_1mt : 0 < 1 - t := sub_pos.mpr ht1
  have hr3_le : r / 3 ≤ r := by linarith only [hr]
  have hy_cl : y ∈ closedBall y₀ r := ball_subset_closedBall (ball_subset_ball hr3_le hy_in)
  have hz_cl : z ∈ closedBall z₀ r := ball_subset_closedBall (ball_subset_ball hr3_le hz_in)
  let g₁ : Space n := q₁ - M • y + p₁
  let g₂ : Space n := q₂ - M • z + p₂
  let x_pt : Space n := t • y + (1 - t) • z
  have hx_in : x_pt ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
    comb_mem_closedBall ht ht1 hy_cl hz_cl
  have hfirst : ∀ h k : Space n, min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤
      t * inner ℝ (gradient φ x_pt) h + (1 - t) * inner ℝ (gradient φ x_pt) k := by
    intro h k
    have hφ_diff : HasGradientAt φ (gradient φ x_pt) x_pt :=
      ((hφ.contDiffAt (hU.mem_nhds (hsub hx_in))).differentiableAt (by norm_num)).hasGradientAt
    have hline_φ : HasDerivAt (fun s : ℝ => φ (x_pt + s • (t • h + (1 - t) • k)))
        (inner ℝ (gradient φ x_pt) (t • h + (1 - t) • k)) 0 := by
      have hlin : HasDerivAt (fun s : ℝ => x_pt + s • (t • h + (1 - t) • k))
          (t • h + (1 - t) • k) (0 : ℝ) := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (t • h + (1 - t) • k)).const_add x_pt
      have hφ0 : HasFDerivAt φ (toDual ℝ (Space n) (gradient φ x_pt))
          (x_pt + (0 : ℝ) • (t • h + (1 - t) • k)) := by
        simpa using hφ_diff.hasFDerivAt
      have h1 := hφ0.comp_hasDerivAt (0 : ℝ) hlin
      rwa [toDual_apply_apply] at h1
    have hlim_lhs : Tendsto (fun s : ℝ => min (inner ℝ g₁ h) (inner ℝ g₂ k) -
        (M / 2) * s * max (‖h‖ ^ 2) (‖k‖ ^ 2)) (𝓝[>] 0) (𝓝 (min (inner ℝ g₁ h) (inner ℝ g₂ k))) := by
      have h1 : Tendsto (fun s : ℝ => min (inner ℝ g₁ h) (inner ℝ g₂ k) -
          (M / 2) * s * max (‖h‖ ^ 2) (‖k‖ ^ 2)) (𝓝 0)
          (𝓝 (min (inner ℝ g₁ h) (inner ℝ g₂ k) - (M / 2) * 0 * max (‖h‖ ^ 2) (‖k‖ ^ 2))) :=
        tendsto_const_nhds.sub (((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto)
      simpa using h1.mono_left nhdsWithin_le_nhds
    have hle_lim : min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤
        inner ℝ (gradient φ x_pt) (t • h + (1 - t) • k) := by
      apply le_of_tendsto_of_tendsto hlim_lhs hline_φ.tendsto_slope_zero_right
      have hden_pos : 0 < max ‖h‖ ‖k‖ + 1 := by
        linarith only [le_max_left ‖h‖ ‖k‖, norm_nonneg h]
      let s₀ : ℝ := (r / 3) / (max ‖h‖ ‖k‖ + 1)
      have hs₀_pos : 0 < s₀ := div_pos (by linarith only [hr]) hden_pos
      filter_upwards [Ioo_mem_nhdsGT hs₀_pos] with s hs
      have hy_s : y + s • h ∈ closedBall y₀ r := by
        rw [mem_closedBall, dist_eq_norm, show y + s • h - y₀ = (y - y₀) + s • h by abel]
        have hy_lt : ‖y - y₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hy_in
        have hsh : s * ‖h‖ ≤ r / 3 := by
          have h2 : s₀ * ‖h‖ ≤ r / 3 := by
            dsimp only [s₀]
            rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
            exact mul_le_mul_of_nonneg_left
              (by linarith only [le_max_left ‖h‖ ‖k‖]) (by linarith only [hr])
          exact (mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)).trans h2
        calc ‖(y - y₀) + s • h‖ ≤ ‖y - y₀‖ + ‖s • h‖ := norm_add_le _ _
          _ = ‖y - y₀‖ + s * ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1.le]
          _ ≤ r := by linarith only [hy_lt, hsh, hr]
      have hz_s : z + s • k ∈ closedBall z₀ r := by
        rw [mem_closedBall, dist_eq_norm, show z + s • k - z₀ = (z - z₀) + s • k by abel]
        have hz_lt : ‖z - z₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hz_in
        have hsk : s * ‖k‖ ≤ r / 3 := by
          have h2 : s₀ * ‖k‖ ≤ r / 3 := by
            dsimp only [s₀]
            rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
            exact mul_le_mul_of_nonneg_left
              (by linarith only [le_max_right ‖h‖ ‖k‖]) (by linarith only [hr])
          exact (mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg _)).trans h2
        calc ‖(z - z₀) + s • k‖ ≤ ‖z - z₀‖ + ‖s • k‖ := norm_add_le _ _
          _ = ‖z - z₀‖ + s * ‖k‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1.le]
          _ ≤ r := by linarith only [hz_lt, hsk, hr]
      have hm := hmax (y + s • h) hy_s (z + s • k) hz_s
      have hpt_eq : t • (y + s • h) + (1 - t) • (z + s • k) =
          x_pt + s • (t • h + (1 - t) • k) := by
        dsimp only [x_pt]; module
      rw [hpt_eq, heq_val, min_self] at hm
      have hu_lo : (u₁ y + inner ℝ p₁ y) + s * inner ℝ g₁ h - (M / 2) * s ^ 2 * ‖h‖ ^ 2 ≤
          u₁ (y + s • h) + inner ℝ p₁ (y + s • h) := by
        have hsub1 := hq₁ (y + s • h)
        dsimp only at hsub1
        rw [add_sub_cancel_left, real_inner_smul_right, norm_add_sq_real, real_inner_smul_right,
          norm_smul, Real.norm_of_nonneg hs.1.le] at hsub1
        rw [inner_add_right, real_inner_smul_right]
        dsimp only [g₁]
        rw [inner_add_left, inner_sub_left, real_inner_smul_left]
        have hsq : (M / 2) * (‖y‖ ^ 2 + 2 * (s * inner ℝ y h) + (s * ‖h‖) ^ 2) =
            (M / 2) * ‖y‖ ^ 2 + s * (M * inner ℝ y h) + (M / 2) * s ^ 2 * ‖h‖ ^ 2 := by ring
        linarith only [hsub1, hsq]
      have hv_lo : (v₁ z + inner ℝ p₂ z + c) + s * inner ℝ g₂ k - (M / 2) * s ^ 2 * ‖k‖ ^ 2 ≤
          v₁ (z + s • k) + inner ℝ p₂ (z + s • k) + c := by
        have hsub2 := hq₂ (z + s • k)
        dsimp only at hsub2
        rw [add_sub_cancel_left, real_inner_smul_right, norm_add_sq_real, real_inner_smul_right,
          norm_smul, Real.norm_of_nonneg hs.1.le] at hsub2
        rw [inner_add_right, real_inner_smul_right]
        dsimp only [g₂]
        rw [inner_add_left, inner_sub_left, real_inner_smul_left]
        have hsq : (M / 2) * (‖z‖ ^ 2 + 2 * (s * inner ℝ z k) + (s * ‖k‖) ^ 2) =
            (M / 2) * ‖z‖ ^ 2 + s * (M * inner ℝ z k) + (M / 2) * s ^ 2 * ‖k‖ ^ 2 := by ring
        linarith only [hsub2, hsq]
      have hmin_lo : (v₁ z + inner ℝ p₂ z + c) + s * min (inner ℝ g₁ h) (inner ℝ g₂ k) -
          (M / 2) * s ^ 2 * max (‖h‖ ^ 2) (‖k‖ ^ 2) ≤
          min (u₁ (y + s • h) + inner ℝ p₁ (y + s • h))
            (v₁ (z + s • k) + inner ℝ p₂ (z + s • k) + c) := by
        have hms_nn : 0 ≤ (M / 2) * s ^ 2 :=
          mul_nonneg (div_nonneg hM.le (by norm_num)) (sq_nonneg s)
        rw [le_min_iff]
        constructor
        · have h1 : s * min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤ s * inner ℝ g₁ h :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hs.1.le
          have h2 : (M / 2) * s ^ 2 * ‖h‖ ^ 2 ≤ (M / 2) * s ^ 2 * max (‖h‖ ^ 2) (‖k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hms_nn
          linarith only [hu_lo, heq_val, h1, h2]
        · have h1 : s * min (inner ℝ g₁ h) (inner ℝ g₂ k) ≤ s * inner ℝ g₂ k :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hs.1.le
          have h2 : (M / 2) * s ^ 2 * ‖k‖ ^ 2 ≤ (M / 2) * s ^ 2 * max (‖h‖ ^ 2) (‖k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) hms_nn
          linarith only [hv_lo, h1, h2]
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      rw [← div_eq_inv_mul, le_div_iff₀ hs.1]
      have hstep : s * (min (inner ℝ g₁ h) (inner ℝ g₂ k) - (M / 2) * s * max (‖h‖ ^ 2) (‖k‖ ^ 2)) =
          s * min (inner ℝ g₁ h) (inner ℝ g₂ k) - (M / 2) * s ^ 2 * max (‖h‖ ^ 2) (‖k‖ ^ 2) := by ring
      linarith only [hm, hmin_lo, hstep]
    simpa [inner_add_right, real_inner_smul_right] using hle_lim
  obtain ⟨a, b, ha, hb, hg₁_eq, hg₂_eq, _, hrec⟩ :=
    first_order_min_alignment ht ht1 (hgrad_ne x_pt hx_in) hfirst
  let d_norm : ℝ := ‖gradient φ x_pt‖
  have hd_pos : 0 < d_norm := norm_pos_iff.mpr (hgrad_ne x_pt hx_in)
  let α : ℝ := t * d_norm / a
  have h1mα : 1 - α = (1 - t) * d_norm / b := by
    have hrec' : 1 / d_norm = t / a + (1 - t) / b := hrec
    have hmul : 1 = t * d_norm / a + (1 - t) * d_norm / b := by
      calc (1 : ℝ) = (1 / d_norm) * d_norm := by field_simp [hd_pos.ne']
        _ = (t / a + (1 - t) / b) * d_norm := by rw [hrec']
        _ = t * d_norm / a + (1 - t) * d_norm / b := by ring
    dsimp only [α]; linarith only [hmul]
  have hν_norm : ‖(-d_norm⁻¹) • gradient φ x_pt‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hd_pos), inv_mul_cancel₀ hd_pos.ne']
  have ha_le : a ≤ C_max := by
    have hg₁_norm : ‖g₁‖ = a := by
      rw [hg₁_eq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ha, hν_norm, mul_one]
    rw [← hg₁_norm]
    have hq₁_le : ‖q₁‖ ≤ (L : ℝ) := hq₁.norm_le hf₁_lip
    calc ‖q₁ - M • y + p₁‖ ≤ ‖q₁ - M • y‖ + ‖p₁‖ := norm_add_le _ _
      _ ≤ (‖q₁‖ + ‖M • y‖) + ‖p₁‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖q₁‖ + M * ‖y‖ + ‖p₁‖ := by rw [norm_smul, Real.norm_of_nonneg hM.le]
      _ ≤ (L : ℝ) + M * R_box + 1 := by
          linarith only [hq₁_le, mul_le_mul_of_nonneg_left hy_norm hM.le, hp₁_le]
      _ ≤ C_max := hC_max_ge
  have hb_le : b ≤ C_max := by
    have hg₂_norm : ‖g₂‖ = b := by
      rw [hg₂_eq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hb, hν_norm, mul_one]
    rw [← hg₂_norm]
    have hq₂_le : ‖q₂‖ ≤ (L : ℝ) := hq₂.norm_le hf₂_lip
    calc ‖q₂ - M • z + p₂‖ ≤ ‖q₂ - M • z‖ + ‖p₂‖ := norm_add_le _ _
      _ ≤ (‖q₂‖ + ‖M • z‖) + ‖p₂‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖q₂‖ + M * ‖z‖ + ‖p₂‖ := by rw [norm_smul, Real.norm_of_nonneg hM.le]
      _ ≤ (L : ℝ) + M * R_box + 1 := by
          linarith only [hq₂_le, mul_le_mul_of_nonneg_left hz_norm hM.le, hp₂_le]
      _ ≤ C_max := hC_max_ge
  have hα_ge : α₀ ≤ α := by
    dsimp only [α]
    calc α₀ ≤ t * d_min / C_max := hα₀_le
      _ ≤ t * d_norm / C_max :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hd_ge x_pt hx_in) ht.le) hC_max.le
      _ ≤ t * d_norm / a := div_le_div_of_nonneg_left (mul_nonneg ht.le hd_pos.le) ha ha_le
  have hα_le : α ≤ 1 - β₀ := by
    have hβ_le : β₀ ≤ 1 - α := by
      rw [h1mα]
      calc β₀ ≤ (1 - t) * d_min / C_max := hβ₀_le
        _ ≤ (1 - t) * d_norm / C_max :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hd_ge x_pt hx_in) ht_pos_1mt.le) hC_max.le
        _ ≤ (1 - t) * d_norm / b :=
            div_le_div_of_nonneg_left (mul_nonneg ht_pos_1mt.le hd_pos.le) hb hb_le
    linarith only [hβ_le]
  refine ⟨α, hα_ge, hα_le, ?_, ?_⟩
  · change g₁ = (t / α) • gradient φ x_pt
    rw [hg₁_eq, smul_smul]; congr 1
    dsimp only [α, d_norm]; field_simp [hd_pos.ne', ha.ne', ht.ne']
  · change g₂ = ((1 - t) / (1 - α)) • gradient φ x_pt
    rw [hg₂_eq, smul_smul]
    rw [h1mα]; congr 1; dsimp only [d_norm]; field_simp [hd_pos.ne', hb.ne', ht_pos_1mt.ne']

/-- Uniform quadratic upper bound for `f₁` at `y` and `f₂` at `z` on the contact set. -/
private theorem envelope_quadratic_upper_bound_on_contact
    {t M : ℝ} (ht : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    {u₁ v₁ φ : Space n → ℝ}
    {y₀ z₀ : Space n} {r : ℝ} (hr : 0 < r)
    {d_min d_max C_lip C_max α₀ β₀ m_min C_shift K₀ ρ₀ Cφ C_step C_upper : ℝ}
    (hC_max : 0 < C_max) (hC_lip_le : C_lip + 1 ≤ C_max)
    (hα₀ : 0 < α₀) (hβ₀ : 0 < β₀)
    (hm_min : 0 < m_min) (hm_min_le_t : m_min ≤ t * d_min) (hm_min_le_1mt : m_min ≤ (1 - t) * d_min)
    (hC_shift : 0 < C_shift) (hC_shift_ge : C_max / m_min + 1 ≤ C_shift)
    (hK₀ : 0 < K₀) (hK₀_ge : M * C_shift ^ 2 / 2 ≤ m_min * K₀)
    (hρ₀_le1 : ρ₀ ≤ r / 6) (hρ₀_le2 : ρ₀ ≤ 1 / K₀) (hρ₀_le3 : ρ₀ ≤ (r / 3) / (C_shift + 1))
    (hCφ : 0 < Cφ) (hC_step_nn : 0 ≤ C_step)
    (hC_step_ge : Cφ * (1 + C_shift) ^ 2 + d_max * K₀ ≤ C_step)
    (hC_upper_ge : C_step / min α₀ β₀ + M / 2 ≤ C_upper)
    (hgrad_ne : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), gradient φ x ≠ 0)
    (hd_ge : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), d_min ≤ ‖gradient φ x‖)
    (hd_le : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), ‖gradient φ x‖ ≤ d_max)
    (hφ_quad : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r),
      ∀ y ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r),
        φ y ≤ φ x + inner ℝ (gradient φ x) (y - x) + Cφ * ‖y - x‖ ^ 2)
    (hu₁_lip_box : ∀ y₁ ∈ closedBall y₀ r, ∀ y₂ ∈ closedBall y₀ r,
      |u₁ y₁ - u₁ y₂| ≤ C_lip * ‖y₁ - y₂‖)
    (hv₁_lip_box : ∀ z₁ ∈ closedBall z₀ r, ∀ z₂ ∈ closedBall z₀ r,
      |v₁ z₁ - v₁ z₂| ≤ C_lip * ‖z₁ - z₂‖)
    {y z p₁ p₂ : Space n} {α c : ℝ}
    (hy_in : y ∈ ball y₀ (r / 3)) (hz_in : z ∈ ball z₀ (r / 3))
    (hα_ge : α₀ ≤ α) (hα_le : α ≤ 1 - β₀)
    (hp₁_le1 : ‖p₁‖ ≤ 1) (hp₂_le1 : ‖p₂‖ ≤ 1)
    (heq_val : u₁ y + inner ℝ p₁ y = v₁ z + inner ℝ p₂ z + c)
    (hmax : ∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
      min (u₁ y' + inner ℝ p₁ y') (v₁ z' + inner ℝ p₂ z' + c) - φ (t • y' + (1 - t) • z') ≤
      min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) - φ (t • y + (1 - t) • z))
    (hq₁_ex : ∃ q₁, IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y q₁)
    (hq₂_ex : ∃ q₂, IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z q₂)
    (hq₁_eq : ∀ q₁, IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y q₁ →
      q₁ - M • y + p₁ = (t / α) • gradient φ (t • y + (1 - t) • z))
    (hq₂_eq : ∀ q₂, IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z q₂ →
      q₂ - M • z + p₂ = ((1 - t) / (1 - α)) • gradient φ (t • y + (1 - t) • z)) :
    (∀ q₁, IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y q₁ → ∀ y' ∈ closedBall y ρ₀,
      (u₁ y' + (M / 2) * ‖y'‖ ^ 2) - (u₁ y + (M / 2) * ‖y‖ ^ 2) ≤
        inner ℝ q₁ (y' - y) + C_upper * ‖y' - y‖ ^ 2) ∧
    (∀ q₂, IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z q₂ → ∀ z' ∈ closedBall z ρ₀,
      (v₁ z' + (M / 2) * ‖z'‖ ^ 2) - (v₁ z + (M / 2) * ‖z‖ ^ 2) ≤
        inner ℝ q₂ (z' - z) + C_upper * ‖z' - z‖ ^ 2) := by
  have ht_pos_1mt : 0 < 1 - t := sub_pos.mpr ht1
  have hr3_le : r / 3 ≤ r := by linarith only [hr]
  have hy_cl : y ∈ closedBall y₀ r := ball_subset_closedBall (ball_subset_ball hr3_le hy_in)
  have hz_cl : z ∈ closedBall z₀ r := ball_subset_closedBall (ball_subset_ball hr3_le hz_in)
  let x_pt : Space n := t • y + (1 - t) • z
  have hx_in : x_pt ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
    comb_mem_closedBall ht ht1 hy_cl hz_cl
  let d := gradient φ x_pt
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr (hgrad_ne x_pt hx_in)
  have hd_ge' : d_min ≤ ‖d‖ := hd_ge x_pt hx_in
  have hd_le' : ‖d‖ ≤ d_max := hd_le x_pt hx_in
  have hα_pos : 0 < α := lt_of_lt_of_le hα₀ hα_ge
  have h1mα_pos : 0 < 1 - α := by linarith only [hα_le, hβ₀]
  have hmin_αβ_pos : 0 < min α₀ β₀ := lt_min hα₀ hβ₀
  have hC_shift_p1_pos : 0 < C_shift + 1 := by linarith only [hC_shift]
  have hM2_nn : 0 ≤ M / 2 := div_nonneg hM.le (by norm_num)
  constructor
  · -- Quadratic upper bound for f₁ at y
    intro q₁ hq₁ y' hy'
    obtain ⟨q₂, hq₂⟩ := hq₂_ex
    have hg₁ := hq₁_eq q₁ hq₁
    have hg₂ := hq₂_eq q₂ hq₂
    have hy'_dist : ‖y' - y‖ ≤ ρ₀ := by simpa [mem_closedBall, dist_eq_norm] using hy'
    have hy'_cl : y' ∈ closedBall y₀ r := by
      rw [mem_closedBall, dist_eq_norm, show y' - y₀ = (y' - y) + (y - y₀) by abel]
      have h1 : ‖y - y₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hy_in
      calc ‖(y' - y) + (y - y₀)‖ ≤ ‖y' - y‖ + ‖y - y₀‖ := norm_add_le _ _
        _ ≤ r := by linarith only [hy'_dist, h1, hρ₀_le1, hr]
    let Δ : ℝ := (u₁ y' + inner ℝ p₁ y') - (u₁ y + inner ℝ p₁ y)
    have hΔ_le : |Δ| ≤ C_max * ‖y' - y‖ := by
      have h1 := hu₁_lip_box y' hy'_cl y hy_cl
      have h2 : |inner ℝ p₁ (y' - y)| ≤ 1 * ‖y' - y‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp₁_le1 (norm_nonneg _))
      have hrew : Δ = (u₁ y' - u₁ y) + inner ℝ p₁ (y' - y) := by
        dsimp only [Δ]; rw [inner_sub_right]; ring
      rw [hrew]
      have h3 : C_lip * ‖y' - y‖ + 1 * ‖y' - y‖ ≤ C_max * ‖y' - y‖ := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_lip_le (norm_nonneg _)
      calc |(u₁ y' - u₁ y) + inner ℝ p₁ (y' - y)|
          ≤ |u₁ y' - u₁ y| + |inner ℝ p₁ (y' - y)| := abs_add_le _ _
        _ ≤ C_lip * ‖y' - y‖ + 1 * ‖y' - y‖ := add_le_add h1 h2
        _ ≤ C_max * ‖y' - y‖ := h3
    let b_val : ℝ := (1 - t) * ‖d‖ / (1 - α)
    have hb_ge : m_min ≤ b_val := by
      have h2 : (1 - t) * d_min ≤ (1 - t) * ‖d‖ := mul_le_mul_of_nonneg_left hd_ge' ht_pos_1mt.le
      have h3 : 1 - α ≤ 1 := by linarith only [hα_pos]
      dsimp only [b_val]
      calc m_min ≤ (1 - t) * ‖d‖ := hm_min_le_1mt.trans h2
        _ = (1 - t) * ‖d‖ / 1 := (div_one _).symm
        _ ≤ (1 - t) * ‖d‖ / (1 - α) :=
            div_le_div_of_nonneg_left (mul_nonneg ht_pos_1mt.le (norm_nonneg _)) h1mα_pos h3
    have hb_pos : 0 < b_val := lt_of_lt_of_le hm_min hb_ge
    let s_shift : ℝ := Δ / b_val + K₀ * ‖y' - y‖ ^ 2
    let z' : Space n := z + (s_shift / ‖d‖) • d
    have hz'_norm : ‖z' - z‖ ≤ C_shift * ‖y' - y‖ := by
      have hdiff : z' - z = (s_shift / ‖d‖) • d := by dsimp only [z']; abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd_pos, div_mul_cancel₀ _ hd_pos.ne']
      have h1 : |Δ / b_val| ≤ (C_max / m_min) * ‖y' - y‖ := by
        rw [abs_div, abs_of_pos hb_pos]
        calc |Δ| / b_val ≤ (C_max * ‖y' - y‖) / b_val := div_le_div_of_nonneg_right hΔ_le hb_pos.le
          _ ≤ (C_max * ‖y' - y‖) / m_min :=
              div_le_div_of_nonneg_left (mul_nonneg hC_max.le (norm_nonneg _)) hm_min hb_ge
          _ = (C_max / m_min) * ‖y' - y‖ := by ring
      have h2 : K₀ * ‖y' - y‖ ^ 2 ≤ 1 * ‖y' - y‖ := by
        have hK1 : K₀ * ‖y' - y‖ ≤ 1 := (le_div_iff₀' hK₀).mp (hy'_dist.trans hρ₀_le2)
        calc K₀ * ‖y' - y‖ ^ 2 = (K₀ * ‖y' - y‖) * ‖y' - y‖ := by ring
          _ ≤ 1 * ‖y' - y‖ := mul_le_mul_of_nonneg_right hK1 (norm_nonneg _)
      have h3 : (C_max / m_min) * ‖y' - y‖ + 1 * ‖y' - y‖ ≤ C_shift * ‖y' - y‖ := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_shift_ge (norm_nonneg _)
      calc |s_shift| ≤ |Δ / b_val| + |K₀ * ‖y' - y‖ ^ 2| := abs_add_le _ _
        _ = |Δ / b_val| + K₀ * ‖y' - y‖ ^ 2 := by rw [abs_of_nonneg (mul_nonneg hK₀.le (sq_nonneg _))]
        _ ≤ (C_max / m_min) * ‖y' - y‖ + 1 * ‖y' - y‖ := add_le_add h1 h2
        _ ≤ C_shift * ‖y' - y‖ := h3
    have hz'_cl : z' ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm, show z' - z₀ = (z' - z) + (z - z₀) by abel]
      have h1 : ‖z - z₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hz_in
      have h2 : C_shift * ‖y' - y‖ ≤ r / 3 := by
        have h3 : (C_shift + 1) * ‖y' - y‖ ≤ r / 3 :=
          (le_div_iff₀' hC_shift_p1_pos).mp (hy'_dist.trans hρ₀_le3)
        have h4 : C_shift * ‖y' - y‖ ≤ (C_shift + 1) * ‖y' - y‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        exact h4.trans h3
      calc ‖(z' - z) + (z - z₀)‖ ≤ ‖z' - z‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ r := by linarith only [hz'_norm, h1, h2, hr]
    have hv_ge_u : u₁ y' + inner ℝ p₁ y' ≤ v₁ z' + inner ℝ p₂ z' + c := by
      have hsub2 := hq₂ z'
      dsimp only at hsub2
      have hnorm2 : ‖z'‖ ^ 2 - ‖z‖ ^ 2 = ‖z' - z‖ ^ 2 + 2 * inner ℝ z (z' - z) := by
        have hvec : z' = (z' - z) + z := by abel
        conv_lhs => rw [hvec, norm_add_sq_real]
        rw [real_inner_comm (z' - z) z]; ring
      have hlin2 : inner ℝ (q₂ - M • z + p₂) (z' - z) = b_val * s_shift := by
        rw [hg₂, show z' - z = (s_shift / ‖d‖) • d by dsimp only [z']; abel,
          real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        dsimp only [b_val]; field_simp [hd_pos.ne', h1mα_pos.ne']; ring
      have hK_ge : (M / 2) * ‖z' - z‖ ^ 2 ≤ b_val * (K₀ * ‖y' - y‖ ^ 2) := by
        have h1 : (M / 2) * ‖z' - z‖ ^ 2 ≤ (M * C_shift ^ 2 / 2) * ‖y' - y‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz'_norm 2) hM2_nn
          linarith only [this,
            show (M / 2) * (C_shift * ‖y' - y‖) ^ 2 = (M * C_shift ^ 2 / 2) * ‖y' - y‖ ^ 2 by ring]
        have h3 : m_min * K₀ ≤ b_val * K₀ := mul_le_mul_of_nonneg_right hb_ge hK₀.le
        have h4 := mul_le_mul_of_nonneg_right (hK₀_ge.trans h3) (sq_nonneg ‖y' - y‖)
        linarith only [h1, h4,
          show b_val * K₀ * ‖y' - y‖ ^ 2 = b_val * (K₀ * ‖y' - y‖ ^ 2) by ring]
      have hrew2 : inner ℝ (q₂ - M • z + p₂) (z' - z) =
          inner ℝ q₂ (z' - z) - M * inner ℝ z (z' - z) + inner ℝ p₂ z' - inner ℝ p₂ z := by
        rw [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right p₂ z' z]; ring
      have hnorm2' : (M / 2) * ‖z'‖ ^ 2 - (M / 2) * ‖z‖ ^ 2 =
          (M / 2) * ‖z' - z‖ ^ 2 + M * inner ℝ z (z' - z) := by
        linear_combination (M / 2) * hnorm2
      have hbs : b_val * s_shift = Δ + b_val * (K₀ * ‖y' - y‖ ^ 2) := by
        dsimp only [s_shift]; field_simp [hb_pos.ne']
      dsimp only [Δ] at hbs
      linarith only [hsub2, hnorm2', hlin2, hK_ge, hrew2, hbs, heq_val]
    have hm := hmax y' hy'_cl z' hz'_cl
    rw [heq_val, min_self, min_eq_left hv_ge_u] at hm
    let x' : Space n := t • y' + (1 - t) • z'
    have hx'_in : x' ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
      comb_mem_closedBall ht ht1 hy'_cl hz'_cl
    have hφ_up := hφ_quad x_pt hx_in x' hx'_in
    have hx'_diff : x' - x_pt = t • (y' - y) + (1 - t) • (z' - z) := by
      dsimp only [x', x_pt]; module
    have hx'_norm : ‖x' - x_pt‖ ≤ (1 + C_shift) * ‖y' - y‖ := by
      rw [hx'_diff]
      calc ‖t • (y' - y) + (1 - t) • (z' - z)‖
          ≤ ‖t • (y' - y)‖ + ‖(1 - t) • (z' - z)‖ := norm_add_le _ _
        _ = t * ‖y' - y‖ + (1 - t) * ‖z' - z‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht_pos_1mt.le]
        _ ≤ 1 * ‖y' - y‖ + 1 * (C_shift * ‖y' - y‖) :=
            add_le_add (mul_le_mul_of_nonneg_right ht1.le (norm_nonneg _))
              (mul_le_mul (by linarith only [ht]) hz'_norm (norm_nonneg _) (by norm_num))
        _ = (1 + C_shift) * ‖y' - y‖ := by ring
    have hlin_φ : inner ℝ d (x' - x_pt) =
        t * inner ℝ d (y' - y) + (1 - α) * Δ + (1 - t) * ‖d‖ * K₀ * ‖y' - y‖ ^ 2 := by
      rw [hx'_diff, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        show z' - z = (s_shift / ‖d‖) • d by dsimp only [z']; abel,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
      dsimp only [s_shift, b_val]
      field_simp [hd_pos.ne', h1mα_pos.ne', ht_pos_1mt.ne']; ring
    have hαΔ : α * Δ ≤ t * inner ℝ d (y' - y) + C_step * ‖y' - y‖ ^ 2 := by
      have h1 : Δ ≤ inner ℝ d (x' - x_pt) + Cφ * ‖x' - x_pt‖ ^ 2 := by
        dsimp only [Δ, d]; linarith only [hm, hφ_up, heq_val]
      have h2 : Cφ * ‖x' - x_pt‖ ^ 2 ≤ Cφ * (1 + C_shift) ^ 2 * ‖y' - y‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx'_norm 2) hCφ.le
        linarith only [this,
          show Cφ * ((1 + C_shift) * ‖y' - y‖) ^ 2 = Cφ * (1 + C_shift) ^ 2 * ‖y' - y‖ ^ 2 by ring]
      have h3 : (1 - t) * ‖d‖ * K₀ ≤ d_max * K₀ := by
        calc (1 - t) * ‖d‖ * K₀
            ≤ 1 * d_max * K₀ := mul_le_mul_of_nonneg_right
              (mul_le_mul (by linarith only [ht]) hd_le' (norm_nonneg _) (by norm_num)) hK₀.le
          _ = d_max * K₀ := by ring
      have h3' : (1 - t) * ‖d‖ * K₀ * ‖y' - y‖ ^ 2 ≤ d_max * K₀ * ‖y' - y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      have h4 : Cφ * (1 + C_shift) ^ 2 * ‖y' - y‖ ^ 2 + d_max * K₀ * ‖y' - y‖ ^ 2 ≤ C_step * ‖y' - y‖ ^ 2 := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_step_ge (sq_nonneg _)
      rw [hlin_φ] at h1
      linarith only [h1, h2, h3', h4]
    have hΔ_bound : Δ ≤ inner ℝ ((t / α) • d) (y' - y) + (C_step / min α₀ β₀) * ‖y' - y‖ ^ 2 := by
      rw [real_inner_smul_left]
      have hdiv : Δ ≤ (t / α) * inner ℝ d (y' - y) + (C_step / α) * ‖y' - y‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
        exact (le_div_iff₀' hα_pos).mpr hαΔ
      have hC_le : C_step / α ≤ C_step / min α₀ β₀ :=
        div_le_div_of_nonneg_left hC_step_nn hmin_αβ_pos ((min_le_left _ _).trans hα_ge)
      linarith only [hdiv, mul_le_mul_of_nonneg_right hC_le (sq_nonneg ‖y' - y‖)]
    have hnorm1 : ‖y'‖ ^ 2 - ‖y‖ ^ 2 = ‖y' - y‖ ^ 2 + 2 * inner ℝ y (y' - y) := by
      have hvec : y' = (y' - y) + y := by abel
      conv_lhs => rw [hvec, norm_add_sq_real]
      rw [real_inner_comm (y' - y) y]; ring
    have hq₁_inner : inner ℝ q₁ (y' - y) =
        inner ℝ ((t / α) • d) (y' - y) + M * inner ℝ y (y' - y) - inner ℝ p₁ (y' - y) := by
      rw [← hg₁, inner_add_left, inner_sub_left, real_inner_smul_left]; ring
    have hf₁_diff : (u₁ y' + (M / 2) * ‖y'‖ ^ 2) - (u₁ y + (M / 2) * ‖y‖ ^ 2) =
        Δ - inner ℝ p₁ (y' - y) + (M / 2) * (‖y'‖ ^ 2 - ‖y‖ ^ 2) := by
      dsimp only [Δ]; rw [inner_sub_right]; ring
    have hnorm1' : (M / 2) * (‖y'‖ ^ 2 - ‖y‖ ^ 2) = (M / 2) * ‖y' - y‖ ^ 2 + M * inner ℝ y (y' - y) := by
      linear_combination (M / 2) * hnorm1
    have hCu : (C_step / min α₀ β₀) * ‖y' - y‖ ^ 2 + (M / 2) * ‖y' - y‖ ^ 2 ≤ C_upper * ‖y' - y‖ ^ 2 := by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_upper_ge (sq_nonneg _)
    rw [hf₁_diff, hnorm1', hq₁_inner]
    linarith only [hΔ_bound, hCu]
  · -- Symmetric quadratic upper bound for f₂ at z
    intro q₂ hq₂ z' hz'
    obtain ⟨q₁, hq₁⟩ := hq₁_ex
    have hg₁ := hq₁_eq q₁ hq₁
    have hg₂ := hq₂_eq q₂ hq₂
    have hz'_dist : ‖z' - z‖ ≤ ρ₀ := by simpa [mem_closedBall, dist_eq_norm] using hz'
    have hz'_cl : z' ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm, show z' - z₀ = (z' - z) + (z - z₀) by abel]
      have h1 : ‖z - z₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hz_in
      calc ‖(z' - z) + (z - z₀)‖ ≤ ‖z' - z‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ r := by linarith only [hz'_dist, h1, hρ₀_le1, hr]
    let Δ : ℝ := (v₁ z' + inner ℝ p₂ z' + c) - (v₁ z + inner ℝ p₂ z + c)
    have hΔ_le : |Δ| ≤ C_max * ‖z' - z‖ := by
      have h1 := hv₁_lip_box z' hz'_cl z hz_cl
      have h2 : |inner ℝ p₂ (z' - z)| ≤ 1 * ‖z' - z‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp₂_le1 (norm_nonneg _))
      have hrew : Δ = (v₁ z' - v₁ z) + inner ℝ p₂ (z' - z) := by
        dsimp only [Δ]; rw [inner_sub_right]; ring
      rw [hrew]
      have h3 : C_lip * ‖z' - z‖ + 1 * ‖z' - z‖ ≤ C_max * ‖z' - z‖ := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_lip_le (norm_nonneg _)
      calc |(v₁ z' - v₁ z) + inner ℝ p₂ (z' - z)|
          ≤ |v₁ z' - v₁ z| + |inner ℝ p₂ (z' - z)| := abs_add_le _ _
        _ ≤ C_lip * ‖z' - z‖ + 1 * ‖z' - z‖ := add_le_add h1 h2
        _ ≤ C_max * ‖z' - z‖ := h3
    let a_val : ℝ := t * ‖d‖ / α
    have ha_ge : m_min ≤ a_val := by
      have h2 : t * d_min ≤ t * ‖d‖ := mul_le_mul_of_nonneg_left hd_ge' ht.le
      have h3 : α ≤ 1 := by linarith only [h1mα_pos]
      dsimp only [a_val]
      calc m_min ≤ t * ‖d‖ := hm_min_le_t.trans h2
        _ = t * ‖d‖ / 1 := (div_one _).symm
        _ ≤ t * ‖d‖ / α := div_le_div_of_nonneg_left (mul_nonneg ht.le (norm_nonneg _)) hα_pos h3
    have ha_pos : 0 < a_val := lt_of_lt_of_le hm_min ha_ge
    let s_shift : ℝ := Δ / a_val + K₀ * ‖z' - z‖ ^ 2
    let y' : Space n := y + (s_shift / ‖d‖) • d
    have hy'_norm : ‖y' - y‖ ≤ C_shift * ‖z' - z‖ := by
      have hdiff : y' - y = (s_shift / ‖d‖) • d := by dsimp only [y']; abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hd_pos, div_mul_cancel₀ _ hd_pos.ne']
      have h1 : |Δ / a_val| ≤ (C_max / m_min) * ‖z' - z‖ := by
        rw [abs_div, abs_of_pos ha_pos]
        calc |Δ| / a_val ≤ (C_max * ‖z' - z‖) / a_val := div_le_div_of_nonneg_right hΔ_le ha_pos.le
          _ ≤ (C_max * ‖z' - z‖) / m_min :=
              div_le_div_of_nonneg_left (mul_nonneg hC_max.le (norm_nonneg _)) hm_min ha_ge
          _ = (C_max / m_min) * ‖z' - z‖ := by ring
      have h2 : K₀ * ‖z' - z‖ ^ 2 ≤ 1 * ‖z' - z‖ := by
        have hK1 : K₀ * ‖z' - z‖ ≤ 1 := (le_div_iff₀' hK₀).mp (hz'_dist.trans hρ₀_le2)
        calc K₀ * ‖z' - z‖ ^ 2 = (K₀ * ‖z' - z‖) * ‖z' - z‖ := by ring
          _ ≤ 1 * ‖z' - z‖ := mul_le_mul_of_nonneg_right hK1 (norm_nonneg _)
      have h3 : (C_max / m_min) * ‖z' - z‖ + 1 * ‖z' - z‖ ≤ C_shift * ‖z' - z‖ := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_shift_ge (norm_nonneg _)
      calc |s_shift| ≤ |Δ / a_val| + |K₀ * ‖z' - z‖ ^ 2| := abs_add_le _ _
        _ = |Δ / a_val| + K₀ * ‖z' - z‖ ^ 2 := by rw [abs_of_nonneg (mul_nonneg hK₀.le (sq_nonneg _))]
        _ ≤ (C_max / m_min) * ‖z' - z‖ + 1 * ‖z' - z‖ := add_le_add h1 h2
        _ ≤ C_shift * ‖z' - z‖ := h3
    have hy'_cl : y' ∈ closedBall y₀ r := by
      rw [mem_closedBall, dist_eq_norm, show y' - y₀ = (y' - y) + (y - y₀) by abel]
      have h1 : ‖y - y₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hy_in
      have h2 : C_shift * ‖z' - z‖ ≤ r / 3 := by
        have h3 : (C_shift + 1) * ‖z' - z‖ ≤ r / 3 :=
          (le_div_iff₀' hC_shift_p1_pos).mp (hz'_dist.trans hρ₀_le3)
        have h4 : C_shift * ‖z' - z‖ ≤ (C_shift + 1) * ‖z' - z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        exact h4.trans h3
      calc ‖(y' - y) + (y - y₀)‖ ≤ ‖y' - y‖ + ‖y - y₀‖ := norm_add_le _ _
        _ ≤ r := by linarith only [hy'_norm, h1, h2, hr]
    have hu_ge_v : v₁ z' + inner ℝ p₂ z' + c ≤ u₁ y' + inner ℝ p₁ y' := by
      have hsub1 := hq₁ y'
      dsimp only at hsub1
      have hnorm1 : ‖y'‖ ^ 2 - ‖y‖ ^ 2 = ‖y' - y‖ ^ 2 + 2 * inner ℝ y (y' - y) := by
        have hvec : y' = (y' - y) + y := by abel
        conv_lhs => rw [hvec, norm_add_sq_real]
        rw [real_inner_comm (y' - y) y]; ring
      have hlin1 : inner ℝ (q₁ - M • y + p₁) (y' - y) = a_val * s_shift := by
        rw [hg₁, show y' - y = (s_shift / ‖d‖) • d by dsimp only [y']; abel,
          real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        dsimp only [a_val]; field_simp [hd_pos.ne', hα_pos.ne']; ring
      have hK_ge : (M / 2) * ‖y' - y‖ ^ 2 ≤ a_val * (K₀ * ‖z' - z‖ ^ 2) := by
        have h1 : (M / 2) * ‖y' - y‖ ^ 2 ≤ (M * C_shift ^ 2 / 2) * ‖z' - z‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy'_norm 2) hM2_nn
          linarith only [this,
            show (M / 2) * (C_shift * ‖z' - z‖) ^ 2 = (M * C_shift ^ 2 / 2) * ‖z' - z‖ ^ 2 by ring]
        have h3 : m_min * K₀ ≤ a_val * K₀ := mul_le_mul_of_nonneg_right ha_ge hK₀.le
        have h4 := mul_le_mul_of_nonneg_right (hK₀_ge.trans h3) (sq_nonneg ‖z' - z‖)
        linarith only [h1, h4,
          show a_val * K₀ * ‖z' - z‖ ^ 2 = a_val * (K₀ * ‖z' - z‖ ^ 2) by ring]
      have hrew1 : inner ℝ (q₁ - M • y + p₁) (y' - y) =
          inner ℝ q₁ (y' - y) - M * inner ℝ y (y' - y) + inner ℝ p₁ y' - inner ℝ p₁ y := by
        rw [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right p₁ y' y]; ring
      have hnorm1' : (M / 2) * ‖y'‖ ^ 2 - (M / 2) * ‖y‖ ^ 2 =
          (M / 2) * ‖y' - y‖ ^ 2 + M * inner ℝ y (y' - y) := by
        linear_combination (M / 2) * hnorm1
      have has : a_val * s_shift = Δ + a_val * (K₀ * ‖z' - z‖ ^ 2) := by
        dsimp only [s_shift]; field_simp [ha_pos.ne']
      dsimp only [Δ] at has
      linarith only [hsub1, hnorm1', hlin1, hK_ge, hrew1, has, heq_val]
    have hm := hmax y' hy'_cl z' hz'_cl
    rw [heq_val, min_self, min_eq_right hu_ge_v] at hm
    let x' : Space n := t • y' + (1 - t) • z'
    have hx'_in : x' ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
      comb_mem_closedBall ht ht1 hy'_cl hz'_cl
    have hφ_up := hφ_quad x_pt hx_in x' hx'_in
    have hx'_diff : x' - x_pt = t • (y' - y) + (1 - t) • (z' - z) := by
      dsimp only [x', x_pt]; module
    have hx'_norm : ‖x' - x_pt‖ ≤ (1 + C_shift) * ‖z' - z‖ := by
      rw [hx'_diff]
      calc ‖t • (y' - y) + (1 - t) • (z' - z)‖
          ≤ ‖t • (y' - y)‖ + ‖(1 - t) • (z' - z)‖ := norm_add_le _ _
        _ = t * ‖y' - y‖ + (1 - t) * ‖z' - z‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht_pos_1mt.le]
        _ ≤ 1 * (C_shift * ‖z' - z‖) + 1 * ‖z' - z‖ :=
            add_le_add (mul_le_mul ht1.le hy'_norm (norm_nonneg _) (by norm_num))
              (mul_le_mul_of_nonneg_right (by linarith only [ht]) (norm_nonneg _))
        _ = (1 + C_shift) * ‖z' - z‖ := by ring
    have hlin_φ : inner ℝ d (x' - x_pt) =
        (1 - t) * inner ℝ d (z' - z) + α * Δ + t * ‖d‖ * K₀ * ‖z' - z‖ ^ 2 := by
      rw [hx'_diff, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        show y' - y = (s_shift / ‖d‖) • d by dsimp only [y']; abel,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
      dsimp only [s_shift, a_val]
      field_simp [hd_pos.ne', hα_pos.ne', ht.ne']; ring
    have h1mαΔ : (1 - α) * Δ ≤ (1 - t) * inner ℝ d (z' - z) + C_step * ‖z' - z‖ ^ 2 := by
      have h1 : Δ ≤ inner ℝ d (x' - x_pt) + Cφ * ‖x' - x_pt‖ ^ 2 := by
        dsimp only [Δ, d]; linarith only [hm, hφ_up]
      have h2 : Cφ * ‖x' - x_pt‖ ^ 2 ≤ Cφ * (1 + C_shift) ^ 2 * ‖z' - z‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx'_norm 2) hCφ.le
        linarith only [this,
          show Cφ * ((1 + C_shift) * ‖z' - z‖) ^ 2 = Cφ * (1 + C_shift) ^ 2 * ‖z' - z‖ ^ 2 by ring]
      have h3 : t * ‖d‖ * K₀ ≤ d_max * K₀ := by
        calc t * ‖d‖ * K₀
            ≤ 1 * d_max * K₀ := mul_le_mul_of_nonneg_right
              (mul_le_mul ht1.le hd_le' (norm_nonneg _) (by norm_num)) hK₀.le
          _ = d_max * K₀ := by ring
      have h3' : t * ‖d‖ * K₀ * ‖z' - z‖ ^ 2 ≤ d_max * K₀ * ‖z' - z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      have h4 : Cφ * (1 + C_shift) ^ 2 * ‖z' - z‖ ^ 2 + d_max * K₀ * ‖z' - z‖ ^ 2 ≤ C_step * ‖z' - z‖ ^ 2 := by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_step_ge (sq_nonneg _)
      rw [hlin_φ] at h1
      linarith only [h1, h2, h3', h4]
    have hΔ_bound : Δ ≤ inner ℝ (((1 - t) / (1 - α)) • d) (z' - z) + (C_step / min α₀ β₀) * ‖z' - z‖ ^ 2 := by
      rw [real_inner_smul_left]
      have hdiv : Δ ≤ ((1 - t) / (1 - α)) * inner ℝ d (z' - z) + (C_step / (1 - α)) * ‖z' - z‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
        exact (le_div_iff₀' h1mα_pos).mpr h1mαΔ
      have hC_le : C_step / (1 - α) ≤ C_step / min α₀ β₀ :=
        div_le_div_of_nonneg_left hC_step_nn hmin_αβ_pos ((min_le_right _ _).trans (by linarith only [hα_le]))
      linarith only [hdiv, mul_le_mul_of_nonneg_right hC_le (sq_nonneg ‖z' - z‖)]
    have hnorm2 : ‖z'‖ ^ 2 - ‖z‖ ^ 2 = ‖z' - z‖ ^ 2 + 2 * inner ℝ z (z' - z) := by
      have hvec : z' = (z' - z) + z := by abel
      conv_lhs => rw [hvec, norm_add_sq_real]
      rw [real_inner_comm (z' - z) z]; ring
    have hq₂_inner : inner ℝ q₂ (z' - z) =
        inner ℝ (((1 - t) / (1 - α)) • d) (z' - z) + M * inner ℝ z (z' - z) - inner ℝ p₂ (z' - z) := by
      rw [← hg₂, inner_add_left, inner_sub_left, real_inner_smul_left]; ring
    have hf₂_diff : (v₁ z' + (M / 2) * ‖z'‖ ^ 2) - (v₁ z + (M / 2) * ‖z‖ ^ 2) =
        Δ - inner ℝ p₂ (z' - z) + (M / 2) * (‖z'‖ ^ 2 - ‖z‖ ^ 2) := by
      dsimp only [Δ]; rw [inner_sub_right]; ring
    have hnorm2' : (M / 2) * (‖z'‖ ^ 2 - ‖z‖ ^ 2) = (M / 2) * ‖z' - z‖ ^ 2 + M * inner ℝ z (z' - z) := by
      linear_combination (M / 2) * hnorm2
    have hCu : (C_step / min α₀ β₀) * ‖z' - z‖ ^ 2 + (M / 2) * ‖z' - z‖ ^ 2 ≤ C_upper * ‖z' - z‖ ^ 2 := by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right hC_upper_ge (sq_nonneg _)
    rw [hf₂_diff, hnorm2', hq₂_inner]
    linarith only [hΔ_bound, hCu]

/-- The contact map `Φ : (y, z, α) ↦ (p₁, p₂, c)` is Lipschitz on `K_con`. -/
private theorem envelope_contact_map_lipschitzOn
    {t M : ℝ} (ht : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    {L L1 L2 : ℝ≥0} {u₁ v₁ φ : Space n → ℝ}
    {y₀ z₀ : Space n} {r : ℝ} (hr : 0 < r)
    {α₀ β₀ R_box d_max Cφ : ℝ}
    (hα₀ : 0 < α₀) (hβ₀ : 0 < β₀) (hR_box : 0 < R_box) (hd_max : 0 < d_max) (hCφ : 0 < Cφ)
    (hgrad_lip : LipschitzOnWith (Real.toNNReal Cφ) (gradient φ) (closedBall (t • y₀ + (1 - t) • z₀) (2 * r)))
    (hd_le : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), ‖gradient φ x‖ ≤ d_max)
    (hy_norm : ∀ y ∈ closedBall y₀ r, ‖y‖ ≤ R_box)
    (hz_norm : ∀ z ∈ closedBall z₀ r, ‖z‖ ≤ R_box)
    (hu₁_lip_box : ∀ y₁ ∈ closedBall y₀ r, ∀ y₂ ∈ closedBall y₀ r,
      |u₁ y₁ - u₁ y₂| ≤ ((L : ℝ) + M * R_box) * ‖y₁ - y₂‖)
    (hv₁_lip_box : ∀ z₁ ∈ closedBall z₀ r, ∀ z₂ ∈ closedBall z₀ r,
      |v₁ z₁ - v₁ z₂| ≤ ((L : ℝ) + M * R_box) * ‖z₁ - z₂‖)
    {Q1 Q2 : Space n → Space n}
    (hQ1_norm : ∀ y, ‖Q1 y‖ ≤ (L : ℝ))
    (hQ2_norm : ∀ z, ‖Q2 z‖ ≤ (L : ℝ))
    {K_con : Set (Q n)}
    (hK_mem : ∀ q ∈ K_con, qY q ∈ ball y₀ (r / 3) ∧ qZ q ∈ ball z₀ (r / 3) ∧ α₀ ≤ qA q ∧ qA q ≤ 1 - β₀)
    (hL1 : LipschitzOnWith L1 Q1 (qY '' K_con))
    (hL2 : LipschitzOnWith L2 Q2 (qZ '' K_con)) :
    let Φ₁ : Q n → Space n := fun q => (t / qA q) • gradient φ (t • qY q + (1 - t) • qZ q) + M • qY q - Q1 (qY q)
    let Φ₂ : Q n → Space n := fun q => ((1 - t) / (1 - qA q)) • gradient φ (t • qY q + (1 - t) • qZ q) + M • qZ q - Q2 (qZ q)
    let Φ₃ : Q n → ℝ := fun q => u₁ (qY q) - v₁ (qZ q) + inner ℝ (Φ₁ q) (qY q) - inner ℝ (Φ₂ q) (qZ q)
    let Φ : Q n → Q n := fun q => WithLp.toLp 2 (WithLp.toLp 2 (Φ₁ q, Φ₂ q), Φ₃ q)
    ∃ LΦ : ℝ≥0, LipschitzOnWith LΦ Φ K_con := by
  intro Φ₁ Φ₂ Φ₃ Φ
  have ht_pos_1mt : 0 < 1 - t := sub_pos.mpr ht1
  let C1 : ℝ := (t / α₀) * Cφ + (t / α₀ ^ 2) * d_max + M + (L1 : ℝ)
  let C2 : ℝ := ((1 - t) / β₀) * Cφ + ((1 - t) / β₀ ^ 2) * d_max + M + (L2 : ℝ)
  let B1 : ℝ := (t / α₀) * d_max + M * R_box + (L : ℝ)
  let B2 : ℝ := ((1 - t) / β₀) * d_max + M * R_box + (L : ℝ)
  let C3 : ℝ := 2 * ((L : ℝ) + M * R_box) + B1 + R_box * C1 + B2 + R_box * C2
  let Ctot : ℝ := C1 + C2 + C3
  have hC1_nn : 0 ≤ C1 := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (div_nonneg ht.le hα₀.le) hCφ.le)
    (mul_nonneg (div_nonneg ht.le (sq_nonneg α₀)) hd_max.le)) hM.le) (NNReal.coe_nonneg L1)
  have hC2_nn : 0 ≤ C2 := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (div_nonneg ht_pos_1mt.le hβ₀.le) hCφ.le)
    (mul_nonneg (div_nonneg ht_pos_1mt.le (sq_nonneg β₀)) hd_max.le)) hM.le) (NNReal.coe_nonneg L2)
  have hB1_nn : 0 ≤ B1 := add_nonneg (add_nonneg
    (mul_nonneg (div_nonneg ht.le hα₀.le) hd_max.le) (mul_nonneg hM.le hR_box.le)) (NNReal.coe_nonneg L)
  have hB2_nn : 0 ≤ B2 := add_nonneg (add_nonneg
    (mul_nonneg (div_nonneg ht_pos_1mt.le hβ₀.le) hd_max.le) (mul_nonneg hM.le hR_box.le)) (NNReal.coe_nonneg L)
  have hC3_nn : 0 ≤ C3 := add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (NNReal.coe_nonneg L) (mul_nonneg hM.le hR_box.le)))
    hB1_nn) (mul_nonneg hR_box.le hC1_nn)) hB2_nn) (mul_nonneg hR_box.le hC2_nn)
  have hCtot_nn : 0 ≤ Ctot := add_nonneg (add_nonneg hC1_nn hC2_nn) hC3_nn
  refine ⟨⟨Ctot, hCtot_nn⟩, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  change dist (Φ a) (Φ b) ≤ Ctot * dist a b
  obtain ⟨ha_y, ha_z, ha_α_ge, ha_α_le⟩ := hK_mem a ha
  obtain ⟨hb_y, hb_z, hb_α_ge, hb_α_le⟩ := hK_mem b hb
  have hr3_le_r : r / 3 ≤ r := by linarith only [hr]
  have ha_y_cl : qY a ∈ closedBall y₀ r := ball_subset_closedBall (ball_subset_ball hr3_le_r ha_y)
  have hb_y_cl : qY b ∈ closedBall y₀ r := ball_subset_closedBall (ball_subset_ball hr3_le_r hb_y)
  have ha_z_cl : qZ a ∈ closedBall z₀ r := ball_subset_closedBall (ball_subset_ball hr3_le_r ha_z)
  have hb_z_cl : qZ b ∈ closedBall z₀ r := ball_subset_closedBall (ball_subset_ball hr3_le_r hb_z)
  have hxa : t • qY a + (1 - t) • qZ a ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
    comb_mem_closedBall ht ht1 ha_y_cl ha_z_cl
  have hxb : t • qY b + (1 - t) • qZ b ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r) :=
    comb_mem_closedBall ht ht1 hb_y_cl hb_z_cl
  have hdy : ‖qY a - qY b‖ ≤ ‖a - b‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hqY_lip.dist_le_mul a b
  have hdz : ‖qZ a - qZ b‖ ≤ ‖a - b‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hqZ_lip.dist_le_mul a b
  have hdA : |qA a - qA b| ≤ ‖a - b‖ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using hqA_lip.dist_le_mul a b
  have hdx : ‖(t • qY a + (1 - t) • qZ a) - (t • qY b + (1 - t) • qZ b)‖ ≤ ‖a - b‖ := by
    rw [show (t • qY a + (1 - t) • qZ a) - (t • qY b + (1 - t) • qZ b) =
      t • (qY a - qY b) + (1 - t) • (qZ a - qZ b) by module]
    calc ‖t • (qY a - qY b) + (1 - t) • (qZ a - qZ b)‖
        ≤ ‖t • (qY a - qY b)‖ + ‖(1 - t) • (qZ a - qZ b)‖ := norm_add_le _ _
      _ = t * ‖qY a - qY b‖ + (1 - t) * ‖qZ a - qZ b‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg ht_pos_1mt.le]
      _ ≤ t * ‖a - b‖ + (1 - t) * ‖a - b‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hdy ht.le) (mul_le_mul_of_nonneg_left hdz ht_pos_1mt.le)
      _ = ‖a - b‖ := by ring
  have hgrad_d : ‖gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)‖ ≤
      Cφ * ‖a - b‖ := by
    have h1 := hgrad_lip.dist_le_mul _ hxa _ hxb
    rw [Real.coe_toNNReal Cφ hCφ.le] at h1
    change dist _ _ ≤ Cφ * dist _ _ at h1
    rw [dist_eq_norm, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hdx hCφ.le)
  have hαa_pos : 0 < qA a := lt_of_lt_of_le hα₀ ha_α_ge
  have hαb_pos : 0 < qA b := lt_of_lt_of_le hα₀ hb_α_ge
  have hβ_le_a : β₀ ≤ 1 - qA a := by linarith only [ha_α_le]
  have hβ_le_b : β₀ ≤ 1 - qA b := by linarith only [hb_α_le]
  have h1mαa_pos : 0 < 1 - qA a := lt_of_lt_of_le hβ₀ hβ_le_a
  have h1mαb_pos : 0 < 1 - qA b := lt_of_lt_of_le hβ₀ hβ_le_b
  have hΦ1_d : ‖Φ₁ a - Φ₁ b‖ ≤ C1 * ‖a - b‖ := by
    have hvec : Φ₁ a - Φ₁ b =
        (t / qA a) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)) +
        (t / qA a - t / qA b) • gradient φ (t • qY b + (1 - t) • qZ b) +
        M • (qY a - qY b) - (Q1 (qY a) - Q1 (qY b)) := by
      dsimp only [Φ₁]; module
    rw [hvec]
    have h1 : ‖(t / qA a) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b))‖ ≤
        (t / α₀) * Cφ * ‖a - b‖ := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht.le hαa_pos.le)]
      have hle : t / qA a ≤ t / α₀ := div_le_div_of_nonneg_left ht.le hα₀ ha_α_ge
      calc (t / qA a) * ‖gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)‖
          ≤ (t / α₀) * (Cφ * ‖a - b‖) := mul_le_mul hle hgrad_d (norm_nonneg _) (div_nonneg ht.le hα₀.le)
        _ = (t / α₀) * Cφ * ‖a - b‖ := by ring
    have h2 : ‖(t / qA a - t / qA b) • gradient φ (t • qY b + (1 - t) • qZ b)‖ ≤
        (t / α₀ ^ 2) * d_max * ‖a - b‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have hsub : |t / qA a - t / qA b| ≤ (t / α₀ ^ 2) * ‖a - b‖ := by
        have hid : t / qA a - t / qA b = t * (qA b - qA a) / (qA a * qA b) := by
          field_simp [hαa_pos.ne', hαb_pos.ne']
        rw [hid, abs_div, abs_mul, abs_of_pos ht, abs_of_pos (mul_pos hαa_pos hαb_pos), abs_sub_comm]
        have hden : α₀ ^ 2 ≤ qA a * qA b := by
          rw [sq]; exact mul_le_mul ha_α_ge hb_α_ge hα₀.le hαa_pos.le
        calc t * |qA a - qA b| / (qA a * qA b)
            ≤ t * ‖a - b‖ / (qA a * qA b) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdA ht.le) (mul_pos hαa_pos hαb_pos).le
          _ ≤ t * ‖a - b‖ / α₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg ht.le (norm_nonneg _)) (sq_pos_of_pos hα₀) hden
          _ = (t / α₀ ^ 2) * ‖a - b‖ := by ring
      calc |t / qA a - t / qA b| * ‖gradient φ (t • qY b + (1 - t) • qZ b)‖
          ≤ ((t / α₀ ^ 2) * ‖a - b‖) * d_max :=
            mul_le_mul hsub (hd_le _ hxb) (norm_nonneg _)
              (mul_nonneg (div_nonneg ht.le (sq_nonneg α₀)) (norm_nonneg _))
        _ = (t / α₀ ^ 2) * d_max * ‖a - b‖ := by ring
    have h3 : ‖M • (qY a - qY b)‖ ≤ M * ‖a - b‖ := by
      rw [norm_smul, Real.norm_of_nonneg hM.le]; exact mul_le_mul_of_nonneg_left hdy hM.le
    have h4 : ‖Q1 (qY a) - Q1 (qY b)‖ ≤ (L1 : ℝ) * ‖a - b‖ := by
      have hl := hL1.dist_le_mul (qY a) ⟨a, ha, rfl⟩ (qY b) ⟨b, hb, rfl⟩
      rw [dist_eq_norm, dist_eq_norm] at hl
      exact hl.trans (mul_le_mul_of_nonneg_left hdy (NNReal.coe_nonneg L1))
    calc _ ≤ ‖(t / qA a) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)) +
              (t / qA a - t / qA b) • gradient φ (t • qY b + (1 - t) • qZ b) + M • (qY a - qY b)‖ +
              ‖Q1 (qY a) - Q1 (qY b)‖ := norm_sub_le _ _
      _ ≤ (‖(t / qA a) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b))‖ +
              ‖(t / qA a - t / qA b) • gradient φ (t • qY b + (1 - t) • qZ b)‖ + ‖M • (qY a - qY b)‖) +
              ‖Q1 (qY a) - Q1 (qY b)‖ :=
            add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
      _ ≤ C1 * ‖a - b‖ := by dsimp only [C1]; linarith only [h1, h2, h3, h4]
  have hΦ2_d : ‖Φ₂ a - Φ₂ b‖ ≤ C2 * ‖a - b‖ := by
    have hvec : Φ₂ a - Φ₂ b =
        ((1 - t) / (1 - qA a)) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)) +
        ((1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)) • gradient φ (t • qY b + (1 - t) • qZ b) +
        M • (qZ a - qZ b) - (Q2 (qZ a) - Q2 (qZ b)) := by
      dsimp only [Φ₂]; module
    rw [hvec]
    have h1 : ‖((1 - t) / (1 - qA a)) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b))‖ ≤
        ((1 - t) / β₀) * Cφ * ‖a - b‖ := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht_pos_1mt.le h1mαa_pos.le)]
      have hle : (1 - t) / (1 - qA a) ≤ (1 - t) / β₀ :=
        div_le_div_of_nonneg_left ht_pos_1mt.le hβ₀ hβ_le_a
      calc ((1 - t) / (1 - qA a)) * ‖gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)‖
          ≤ ((1 - t) / β₀) * (Cφ * ‖a - b‖) := mul_le_mul hle hgrad_d (norm_nonneg _) (div_nonneg ht_pos_1mt.le hβ₀.le)
        _ = ((1 - t) / β₀) * Cφ * ‖a - b‖ := by ring
    have h2 : ‖((1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)) • gradient φ (t • qY b + (1 - t) • qZ b)‖ ≤
        ((1 - t) / β₀ ^ 2) * d_max * ‖a - b‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have hsub : |(1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)| ≤ ((1 - t) / β₀ ^ 2) * ‖a - b‖ := by
        have hid : (1 - t) / (1 - qA a) - (1 - t) / (1 - qA b) =
            (1 - t) * (qA a - qA b) / ((1 - qA a) * (1 - qA b)) := by
          field_simp [h1mαa_pos.ne', h1mαb_pos.ne']; ring
        rw [hid, abs_div, abs_mul, abs_of_pos ht_pos_1mt, abs_of_pos (mul_pos h1mαa_pos h1mαb_pos)]
        have hden : β₀ ^ 2 ≤ (1 - qA a) * (1 - qA b) := by
          rw [sq]; exact mul_le_mul hβ_le_a hβ_le_b hβ₀.le h1mαa_pos.le
        calc (1 - t) * |qA a - qA b| / ((1 - qA a) * (1 - qA b))
            ≤ (1 - t) * ‖a - b‖ / ((1 - qA a) * (1 - qA b)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdA ht_pos_1mt.le) (mul_pos h1mαa_pos h1mαb_pos).le
          _ ≤ (1 - t) * ‖a - b‖ / β₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg ht_pos_1mt.le (norm_nonneg _)) (sq_pos_of_pos hβ₀) hden
          _ = ((1 - t) / β₀ ^ 2) * ‖a - b‖ := by ring
      calc |(1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)| * ‖gradient φ (t • qY b + (1 - t) • qZ b)‖
          ≤ (((1 - t) / β₀ ^ 2) * ‖a - b‖) * d_max :=
            mul_le_mul hsub (hd_le _ hxb) (norm_nonneg _)
              (mul_nonneg (div_nonneg ht_pos_1mt.le (sq_nonneg β₀)) (norm_nonneg _))
        _ = ((1 - t) / β₀ ^ 2) * d_max * ‖a - b‖ := by ring
    have h3 : ‖M • (qZ a - qZ b)‖ ≤ M * ‖a - b‖ := by
      rw [norm_smul, Real.norm_of_nonneg hM.le]; exact mul_le_mul_of_nonneg_left hdz hM.le
    have h4 : ‖Q2 (qZ a) - Q2 (qZ b)‖ ≤ (L2 : ℝ) * ‖a - b‖ := by
      have hl := hL2.dist_le_mul (qZ a) ⟨a, ha, rfl⟩ (qZ b) ⟨b, hb, rfl⟩
      rw [dist_eq_norm, dist_eq_norm] at hl
      exact hl.trans (mul_le_mul_of_nonneg_left hdz (NNReal.coe_nonneg L2))
    calc _ ≤ ‖((1 - t) / (1 - qA a)) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b)) +
              ((1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)) • gradient φ (t • qY b + (1 - t) • qZ b) + M • (qZ a - qZ b)‖ +
              ‖Q2 (qZ a) - Q2 (qZ b)‖ := norm_sub_le _ _
      _ ≤ (‖((1 - t) / (1 - qA a)) • (gradient φ (t • qY a + (1 - t) • qZ a) - gradient φ (t • qY b + (1 - t) • qZ b))‖ +
              ‖((1 - t) / (1 - qA a) - (1 - t) / (1 - qA b)) • gradient φ (t • qY b + (1 - t) • qZ b)‖ + ‖M • (qZ a - qZ b)‖) +
              ‖Q2 (qZ a) - Q2 (qZ b)‖ :=
            add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
      _ ≤ C2 * ‖a - b‖ := by dsimp only [C2]; linarith only [h1, h2, h3, h4]
  have hΦ1_a : ‖Φ₁ a‖ ≤ B1 := by
    dsimp only [Φ₁, B1]
    have h1 : ‖(t / qA a) • gradient φ (t • qY a + (1 - t) • qZ a)‖ ≤ (t / α₀) * d_max := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht.le hαa_pos.le)]
      exact mul_le_mul (div_le_div_of_nonneg_left ht.le hα₀ ha_α_ge) (hd_le _ hxa) (norm_nonneg _) (div_nonneg ht.le hα₀.le)
    have h2 : ‖M • qY a‖ ≤ M * R_box := by
      rw [norm_smul, Real.norm_of_nonneg hM.le]; exact mul_le_mul_of_nonneg_left (hy_norm _ ha_y_cl) hM.le
    have h3 : ‖Q1 (qY a)‖ ≤ (L : ℝ) := hQ1_norm (qY a)
    calc ‖(t / qA a) • gradient φ (t • qY a + (1 - t) • qZ a) + M • qY a - Q1 (qY a)‖
        ≤ ‖(t / qA a) • gradient φ (t • qY a + (1 - t) • qZ a) + M • qY a‖ + ‖Q1 (qY a)‖ := norm_sub_le _ _
      _ ≤ ‖(t / qA a) • gradient φ (t • qY a + (1 - t) • qZ a)‖ + ‖M • qY a‖ + ‖Q1 (qY a)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (t / α₀) * d_max + M * R_box + (L : ℝ) := by linarith only [h1, h2, h3]
  have hΦ2_a : ‖Φ₂ a‖ ≤ B2 := by
    dsimp only [Φ₂, B2]
    have h1 : ‖((1 - t) / (1 - qA a)) • gradient φ (t • qY a + (1 - t) • qZ a)‖ ≤ ((1 - t) / β₀) * d_max := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht_pos_1mt.le h1mαa_pos.le)]
      exact mul_le_mul (div_le_div_of_nonneg_left ht_pos_1mt.le hβ₀ hβ_le_a)
        (hd_le _ hxa) (norm_nonneg _) (div_nonneg ht_pos_1mt.le hβ₀.le)
    have h2 : ‖M • qZ a‖ ≤ M * R_box := by
      rw [norm_smul, Real.norm_of_nonneg hM.le]; exact mul_le_mul_of_nonneg_left (hz_norm _ ha_z_cl) hM.le
    have h3 : ‖Q2 (qZ a)‖ ≤ (L : ℝ) := hQ2_norm (qZ a)
    calc ‖((1 - t) / (1 - qA a)) • gradient φ (t • qY a + (1 - t) • qZ a) + M • qZ a - Q2 (qZ a)‖
        ≤ ‖((1 - t) / (1 - qA a)) • gradient φ (t • qY a + (1 - t) • qZ a) + M • qZ a‖ + ‖Q2 (qZ a)‖ := norm_sub_le _ _
      _ ≤ ‖((1 - t) / (1 - qA a)) • gradient φ (t • qY a + (1 - t) • qZ a)‖ + ‖M • qZ a‖ + ‖Q2 (qZ a)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((1 - t) / β₀) * d_max + M * R_box + (L : ℝ) := by linarith only [h1, h2, h3]
  have hΦ3_d : |Φ₃ a - Φ₃ b| ≤ C3 * ‖a - b‖ := by
    have hid : Φ₃ a - Φ₃ b =
        (u₁ (qY a) - u₁ (qY b)) - (v₁ (qZ a) - v₁ (qZ b)) +
        inner ℝ (Φ₁ a) (qY a - qY b) + inner ℝ (Φ₁ a - Φ₁ b) (qY b) -
        inner ℝ (Φ₂ a) (qZ a - qZ b) - inner ℝ (Φ₂ a - Φ₂ b) (qZ b) := by
      have hi1 : inner ℝ (Φ₁ a) (qY a - qY b) = inner ℝ (Φ₁ a) (qY a) - inner ℝ (Φ₁ a) (qY b) :=
        inner_sub_right _ _ _
      have hi2 : inner ℝ (Φ₁ a - Φ₁ b) (qY b) = inner ℝ (Φ₁ a) (qY b) - inner ℝ (Φ₁ b) (qY b) :=
        inner_sub_left _ _ _
      have hi3 : inner ℝ (Φ₂ a) (qZ a - qZ b) = inner ℝ (Φ₂ a) (qZ a) - inner ℝ (Φ₂ a) (qZ b) :=
        inner_sub_right _ _ _
      have hi4 : inner ℝ (Φ₂ a - Φ₂ b) (qZ b) = inner ℝ (Φ₂ a) (qZ b) - inner ℝ (Φ₂ b) (qZ b) :=
        inner_sub_left _ _ _
      dsimp only [Φ₃]; linarith only [hi1, hi2, hi3, hi4]
    rw [hid]
    have h1 : |u₁ (qY a) - u₁ (qY b)| ≤ ((L : ℝ) + M * R_box) * ‖a - b‖ :=
      (hu₁_lip_box _ ha_y_cl _ hb_y_cl).trans (mul_le_mul_of_nonneg_left hdy (add_nonneg (NNReal.coe_nonneg L) (mul_nonneg hM.le hR_box.le)))
    have h2 : |v₁ (qZ a) - v₁ (qZ b)| ≤ ((L : ℝ) + M * R_box) * ‖a - b‖ :=
      (hv₁_lip_box _ ha_z_cl _ hb_z_cl).trans (mul_le_mul_of_nonneg_left hdz (add_nonneg (NNReal.coe_nonneg L) (mul_nonneg hM.le hR_box.le)))
    have h3 : |inner ℝ (Φ₁ a) (qY a - qY b)| ≤ B1 * ‖a - b‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hΦ1_a hdy (norm_nonneg _) hB1_nn)
    have h4 : |inner ℝ (Φ₁ a - Φ₁ b) (qY b)| ≤ (R_box * C1) * ‖a - b‖ := by
      calc |inner ℝ (Φ₁ a - Φ₁ b) (qY b)| ≤ ‖Φ₁ a - Φ₁ b‖ * ‖qY b‖ := abs_real_inner_le_norm _ _
        _ ≤ (C1 * ‖a - b‖) * R_box := mul_le_mul hΦ1_d (hy_norm _ hb_y_cl) (norm_nonneg _) (mul_nonneg hC1_nn (norm_nonneg _))
        _ = (R_box * C1) * ‖a - b‖ := by ring
    have h5 : |inner ℝ (Φ₂ a) (qZ a - qZ b)| ≤ B2 * ‖a - b‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hΦ2_a hdz (norm_nonneg _) hB2_nn)
    have h6 : |inner ℝ (Φ₂ a - Φ₂ b) (qZ b)| ≤ (R_box * C2) * ‖a - b‖ := by
      calc |inner ℝ (Φ₂ a - Φ₂ b) (qZ b)| ≤ ‖Φ₂ a - Φ₂ b‖ * ‖qZ b‖ := abs_real_inner_le_norm _ _
        _ ≤ (C2 * ‖a - b‖) * R_box := mul_le_mul hΦ2_d (hz_norm _ hb_z_cl) (norm_nonneg _) (mul_nonneg hC2_nn (norm_nonneg _))
        _ = (R_box * C2) * ‖a - b‖ := by ring
    have habs := abs_sub ((u₁ (qY a) - u₁ (qY b)) - (v₁ (qZ a) - v₁ (qZ b)) +
        inner ℝ (Φ₁ a) (qY a - qY b) + inner ℝ (Φ₁ a - Φ₁ b) (qY b) - inner ℝ (Φ₂ a) (qZ a - qZ b))
        (inner ℝ (Φ₂ a - Φ₂ b) (qZ b))
    have habs2 := abs_sub ((u₁ (qY a) - u₁ (qY b)) - (v₁ (qZ a) - v₁ (qZ b)) +
        inner ℝ (Φ₁ a) (qY a - qY b) + inner ℝ (Φ₁ a - Φ₁ b) (qY b)) (inner ℝ (Φ₂ a) (qZ a - qZ b))
    have habs3 := abs_add_le ((u₁ (qY a) - u₁ (qY b)) - (v₁ (qZ a) - v₁ (qZ b)) +
        inner ℝ (Φ₁ a) (qY a - qY b)) (inner ℝ (Φ₁ a - Φ₁ b) (qY b))
    have habs4 := abs_add_le ((u₁ (qY a) - u₁ (qY b)) - (v₁ (qZ a) - v₁ (qZ b)))
        (inner ℝ (Φ₁ a) (qY a - qY b))
    have habs5 := abs_sub (u₁ (qY a) - u₁ (qY b)) (v₁ (qZ a) - v₁ (qZ b))
    dsimp only [C3]
    linarith only [h1, h2, h3, h4, h5, h6, habs, habs2, habs3, habs4, habs5]
  rw [dist_eq_norm, dist_eq_norm]
  have hnorm_le : ‖Φ a - Φ b‖ ≤ ‖Φ₁ a - Φ₁ b‖ + ‖Φ₂ a - Φ₂ b‖ + |Φ₃ a - Φ₃ b| := by
    have hsq : ‖Φ a - Φ b‖ ^ 2 = ‖Φ₁ a - Φ₁ b‖ ^ 2 + ‖Φ₂ a - Φ₂ b‖ ^ 2 + |Φ₃ a - Φ₃ b| ^ 2 := by
      have h := hnorm_sq_Q (Φ a - Φ b)
      simpa only [qY, qZ, qA, Φ, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub,
        WithLp.ofLp_toLp, Real.norm_eq_abs] using h
    have hnonneg : 0 ≤ ‖Φ₁ a - Φ₁ b‖ + ‖Φ₂ a - Φ₂ b‖ + |Φ₃ a - Φ₃ b| :=
      add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)
    have hsq_le : ‖Φ a - Φ b‖ ^ 2 ≤ (‖Φ₁ a - Φ₁ b‖ + ‖Φ₂ a - Φ₂ b‖ + |Φ₃ a - Φ₃ b|) ^ 2 := by
      rw [hsq]
      have h12 : 0 ≤ ‖Φ₁ a - Φ₁ b‖ * ‖Φ₂ a - Φ₂ b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have h13 : 0 ≤ ‖Φ₁ a - Φ₁ b‖ * |Φ₃ a - Φ₃ b| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
      have h23 : 0 ≤ ‖Φ₂ a - Φ₂ b‖ * |Φ₃ a - Φ₃ b| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
      have hexp : (‖Φ₁ a - Φ₁ b‖ + ‖Φ₂ a - Φ₂ b‖ + |Φ₃ a - Φ₃ b|) ^ 2 =
          ‖Φ₁ a - Φ₁ b‖ ^ 2 + ‖Φ₂ a - Φ₂ b‖ ^ 2 + |Φ₃ a - Φ₃ b| ^ 2 +
          2 * (‖Φ₁ a - Φ₁ b‖ * ‖Φ₂ a - Φ₂ b‖) + 2 * (‖Φ₁ a - Φ₁ b‖ * |Φ₃ a - Φ₃ b|) +
          2 * (‖Φ₂ a - Φ₂ b‖ * |Φ₃ a - Φ₃ b|) := by ring
      linarith only [h12, h13, h23, hexp]
    have habs_le : abs ‖Φ a - Φ b‖ ≤ abs (‖Φ₁ a - Φ₁ b‖ + ‖Φ₂ a - Φ₂ b‖ + |Φ₃ a - Φ₃ b|) :=
      sq_le_sq.mp hsq_le
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnonneg] at habs_le
  dsimp only [Ctot]
  linarith only [hnorm_le, hΦ1_d, hΦ2_d, hΦ3_d]

/-- **The `(2n + 1)`-dimensional perturbation lemma for the sup-min envelope**:
given two semiconvex functions `u₁, v₁` and a noncritical `C²` test `φ` such
that `min(u₁ y, v₁ z) - φ(t•y + (1-t)•z)` has a strict maximum on
`closedBall y₀ r × closedBall z₀ r` at `(y₀, z₀)`, there exist uniform
`ρ₀, C_upper > 0` such that for every `δ > 0` and any full-measure sets
`A₁, A₂`, there exist `(p₁, p₂, c)` with `‖p₁‖, ‖p₂‖, |c| < δ` and an
interior maximizer `(y, z) ∈ (ball y₀ (r/3) ∩ A₁) × (ball z₀ (r/3) ∩ A₂)`
with equal values and uniform quadratic upper bounds on `f₁, f₂`. -/
theorem envelope_jensen_exists_good_maximizer (hn : 2 ≤ n)
    {t M : ℝ} (ht : 0 < t) (ht1 : t < 1) (hM : 0 < M)
    {L : ℝ≥0} {u₁ v₁ φ : Space n → ℝ}
    (hf₁_conv : ConvexOn ℝ univ (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2))
    (hf₁_lip : LipschitzWith L (fun y => u₁ y + (M / 2) * ‖y‖ ^ 2))
    (hf₂_conv : ConvexOn ℝ univ (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2))
    (hf₂_lip : LipschitzWith L (fun z => v₁ z + (M / 2) * ‖z‖ ^ 2))
    {y₀ z₀ : Space n} {r : ℝ} (hr : 0 < r)
    {U : Set (Space n)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hsub : closedBall (t • y₀ + (1 - t) • z₀) (2 * r) ⊆ U)
    (hgrad_ne : ∀ x ∈ closedBall (t • y₀ + (1 - t) • z₀) (2 * r), gradient φ x ≠ 0)
    (hstrict : ∀ y ∈ closedBall y₀ r, ∀ z ∈ closedBall z₀ r, (y, z) ≠ (y₀, z₀) →
      min (u₁ y) (v₁ z) - φ (t • y + (1 - t) • z) <
        min (u₁ y₀) (v₁ z₀) - φ (t • y₀ + (1 - t) • z₀))
    {A₁ A₂ : Set (Space n)} (hA₁ : volume A₁ᶜ = 0) (hA₂ : volume A₂ᶜ = 0) :
    ∃ (ρ₀ C_upper : ℝ), 0 < ρ₀ ∧ 0 < C_upper ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ (p₁ p₂ : Space n) (c : ℝ) (y z : Space n),
          ‖p₁‖ < δ ∧ ‖p₂‖ < δ ∧ |c| < δ ∧
          y ∈ ball y₀ (r / 3) ∧ z ∈ ball z₀ (r / 3) ∧
          y ∈ A₁ ∧ z ∈ A₂ ∧
          u₁ y + inner ℝ p₁ y = v₁ z + inner ℝ p₂ z + c ∧
          (∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
            min (u₁ y' + inner ℝ p₁ y') (v₁ z' + inner ℝ p₂ z' + c) - φ (t • y' + (1 - t) • z') ≤
            min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) - φ (t • y + (1 - t) • z)) ∧
          (∀ q₁ : Space n, IsSubgradient (fun y' => u₁ y' + (M / 2) * ‖y'‖ ^ 2) y q₁ →
            ∀ y' ∈ closedBall y ρ₀,
              (u₁ y' + (M / 2) * ‖y'‖ ^ 2) - (u₁ y + (M / 2) * ‖y‖ ^ 2) ≤
                inner ℝ q₁ (y' - y) + C_upper * ‖y' - y‖ ^ 2) ∧
          (∀ q₂ : Space n, IsSubgradient (fun z' => v₁ z' + (M / 2) * ‖z'‖ ^ 2) z q₂ →
            ∀ z' ∈ closedBall z ρ₀,
              (v₁ z' + (M / 2) * ‖z'‖ ^ 2) - (v₁ z + (M / 2) * ‖z‖ ^ 2) ≤
                inner ℝ q₂ (z' - z) + C_upper * ‖z' - z‖ ^ 2) := by
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : Nontrivial (Space n) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ 1, ?_⟩⟩
    intro h0
    have := congrArg (fun x : Space n => x.ofLp ⟨0, by omega⟩) h0
    simp at this
  let x₀ : Space n := t • y₀ + (1 - t) • z₀
  let f₁ : Space n → ℝ := fun y => u₁ y + (M / 2) * ‖y‖ ^ 2
  let f₂ : Space n → ℝ := fun z => v₁ z + (M / 2) * ‖z‖ ^ 2
  have hu₁_cont : Continuous u₁ := by
    have h1 : Continuous (fun y : Space n => (u₁ y + (M / 2) * ‖y‖ ^ 2) - (M / 2) * ‖y‖ ^ 2) :=
      hf₁_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
    simpa only [add_sub_cancel_right] using h1
  have hv₁_cont : Continuous v₁ := by
    have h1 : Continuous (fun z : Space n => (v₁ z + (M / 2) * ‖z‖ ^ 2) - (M / 2) * ‖z‖ ^ 2) :=
      hf₂_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
    simpa only [add_sub_cancel_right] using h1
  -- Uniform C² bounds on φ on closedBall x₀ (2 * r)
  obtain ⟨Cφ, hCφ, hgrad_lip, hφ_quad⟩ := c2_quadratic_upper_bound hU hφ (by positivity : 0 < 2 * r) hsub
  have hgrad_cont : ContinuousOn (gradient φ) (closedBall x₀ (2 * r)) := hgrad_lip.continuousOn
  have hcomp_x : IsCompact (closedBall x₀ (2 * r)) := isCompact_closedBall x₀ (2 * r)
  have hne_x : (closedBall x₀ (2 * r)).Nonempty := nonempty_closedBall.mpr (by positivity)
  obtain ⟨xm, hxm_mem, hxm_min⟩ := hcomp_x.exists_isMinOn hne_x hgrad_cont.norm
  let d_min : ℝ := ‖gradient φ xm‖
  have hd_min : 0 < d_min := norm_pos_iff.mpr (hgrad_ne xm hxm_mem)
  have hd_ge : ∀ x ∈ closedBall x₀ (2 * r), d_min ≤ ‖gradient φ x‖ := fun x hx => hxm_min hx
  obtain ⟨xM, -, hxM_max⟩ := hcomp_x.exists_isMaxOn hne_x hgrad_cont.norm
  let d_max : ℝ := ‖gradient φ xM‖ + 1
  have hd_max : 0 < d_max := by positivity
  have hd_le : ∀ x ∈ closedBall x₀ (2 * r), ‖gradient φ x‖ ≤ d_max := fun x hx => by
    have : ‖gradient φ x‖ ≤ ‖gradient φ xM‖ := hxM_max hx
    dsimp only [d_max]; linarith
  -- Uniform radius R_box bounding closedBall y₀ r and closedBall z₀ r
  let R_box : ℝ := max ‖y₀‖ ‖z₀‖ + r + 1
  have hR_box : 0 < R_box := by positivity
  have hy_norm (y : Space n) (hy : y ∈ closedBall y₀ r) : ‖y‖ ≤ R_box := by
    have h1 : ‖y - y₀‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hy
    have h2 := norm_add_le (y - y₀) y₀; rw [sub_add_cancel] at h2
    have h3 : ‖y₀‖ ≤ max ‖y₀‖ ‖z₀‖ := le_max_left _ _
    dsimp only [R_box]; linarith
  have hz_norm (z : Space n) (hz : z ∈ closedBall z₀ r) : ‖z‖ ≤ R_box := by
    have h1 : ‖z - z₀‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have h2 := norm_add_le (z - z₀) z₀; rw [sub_add_cancel] at h2
    have h3 : ‖z₀‖ ≤ max ‖y₀‖ ‖z₀‖ := le_max_right _ _
    dsimp only [R_box]; linarith
  -- Uniform Lipschitz constant for u₁ and v₁ on closedBall
  let C_max : ℝ := (L : ℝ) + M * R_box + 2
  have hC_max : 0 < C_max := by positivity
  have hu₁_lip_box : ∀ y₁ ∈ closedBall y₀ r, ∀ y₂ ∈ closedBall y₀ r,
      |u₁ y₁ - u₁ y₂| ≤ ((L : ℝ) + M * R_box) * ‖y₁ - y₂‖ := by
    intro y₁ hy₁ y₂ hy₂
    have h1 : |f₁ y₁ - f₁ y₂| ≤ (L : ℝ) * ‖y₁ - y₂‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hf₁_lip.dist_le_mul y₁ y₂
    have h2 : |‖y₁‖ ^ 2 - ‖y₂‖ ^ 2| ≤ 2 * R_box * ‖y₁ - y₂‖ := by
      have hfac : ‖y₁‖ ^ 2 - ‖y₂‖ ^ 2 = (‖y₁‖ - ‖y₂‖) * (‖y₁‖ + ‖y₂‖) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have ha : |‖y₁‖ - ‖y₂‖| ≤ ‖y₁ - y₂‖ := abs_norm_sub_norm_le y₁ y₂
      have hb : ‖y₁‖ + ‖y₂‖ ≤ 2 * R_box := by linarith [hy_norm y₁ hy₁, hy_norm y₂ hy₂]
      calc |‖y₁‖ - ‖y₂‖| * (‖y₁‖ + ‖y₂‖) ≤ ‖y₁ - y₂‖ * (2 * R_box) :=
            mul_le_mul ha hb (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * R_box * ‖y₁ - y₂‖ := by ring
    have hdiff : u₁ y₁ - u₁ y₂ = (f₁ y₁ - f₁ y₂) - (M / 2) * (‖y₁‖ ^ 2 - ‖y₂‖ ^ 2) := by
      dsimp only [f₁]; ring
    rw [hdiff]
    calc |(f₁ y₁ - f₁ y₂) - (M / 2) * (‖y₁‖ ^ 2 - ‖y₂‖ ^ 2)|
        ≤ |f₁ y₁ - f₁ y₂| + |(M / 2) * (‖y₁‖ ^ 2 - ‖y₂‖ ^ 2)| := abs_sub _ _
      _ = |f₁ y₁ - f₁ y₂| + (M / 2) * |‖y₁‖ ^ 2 - ‖y₂‖ ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ M / 2)]
      _ ≤ (L : ℝ) * ‖y₁ - y₂‖ + (M / 2) * (2 * R_box * ‖y₁ - y₂‖) := by gcongr
      _ = ((L : ℝ) + M * R_box) * ‖y₁ - y₂‖ := by ring
  have hv₁_lip_box : ∀ z₁ ∈ closedBall z₀ r, ∀ z₂ ∈ closedBall z₀ r,
      |v₁ z₁ - v₁ z₂| ≤ ((L : ℝ) + M * R_box) * ‖z₁ - z₂‖ := by
    intro z₁ hz₁ z₂ hz₂
    have h1 : |f₂ z₁ - f₂ z₂| ≤ (L : ℝ) * ‖z₁ - z₂‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hf₂_lip.dist_le_mul z₁ z₂
    have h2 : |‖z₁‖ ^ 2 - ‖z₂‖ ^ 2| ≤ 2 * R_box * ‖z₁ - z₂‖ := by
      have hfac : ‖z₁‖ ^ 2 - ‖z₂‖ ^ 2 = (‖z₁‖ - ‖z₂‖) * (‖z₁‖ + ‖z₂‖) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have ha : |‖z₁‖ - ‖z₂‖| ≤ ‖z₁ - z₂‖ := abs_norm_sub_norm_le z₁ z₂
      have hb : ‖z₁‖ + ‖z₂‖ ≤ 2 * R_box := by linarith [hz_norm z₁ hz₁, hz_norm z₂ hz₂]
      calc |‖z₁‖ - ‖z₂‖| * (‖z₁‖ + ‖z₂‖) ≤ ‖z₁ - z₂‖ * (2 * R_box) :=
            mul_le_mul ha hb (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * R_box * ‖z₁ - z₂‖ := by ring
    have hdiff : v₁ z₁ - v₁ z₂ = (f₂ z₁ - f₂ z₂) - (M / 2) * (‖z₁‖ ^ 2 - ‖z₂‖ ^ 2) := by
      dsimp only [f₂]; ring
    rw [hdiff]
    calc |(f₂ z₁ - f₂ z₂) - (M / 2) * (‖z₁‖ ^ 2 - ‖z₂‖ ^ 2)|
        ≤ |f₂ z₁ - f₂ z₂| + |(M / 2) * (‖z₁‖ ^ 2 - ‖z₂‖ ^ 2)| := abs_sub _ _
      _ = |f₂ z₁ - f₂ z₂| + (M / 2) * |‖z₁‖ ^ 2 - ‖z₂‖ ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ M / 2)]
      _ ≤ (L : ℝ) * ‖z₁ - z₂‖ + (M / 2) * (2 * R_box * ‖z₁ - z₂‖) := by gcongr
      _ = ((L : ℝ) + M * R_box) * ‖z₁ - z₂‖ := by ring
  -- Uniform lower bounds α₀, β₀ and quadratic upper bound constants
  let α₀ : ℝ := t * d_min / C_max
  let β₀ : ℝ := (1 - t) * d_min / C_max
  have hα₀ : 0 < α₀ := by positivity
  have hβ₀ : 0 < β₀ := by positivity
  have ht_pos_1mt : 0 < 1 - t := sub_pos.mpr ht1
  let m_min : ℝ := min (t * d_min) ((1 - t) * d_min)
  have hm_min : 0 < m_min := lt_min (by positivity) (by positivity)
  let C_shift : ℝ := C_max / m_min + 1
  have hC_shift : 0 < C_shift := by positivity
  let K₀ : ℝ := M * C_shift ^ 2 / (2 * m_min) + 1
  have hK₀ : 0 < K₀ := by positivity
  let ρ₀ : ℝ := min (r / 6) (min (1 / K₀) ((r / 3) / (C_shift + 1)))
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  let C_step : ℝ := Cφ * (1 + C_shift) ^ 2 + d_max * K₀ + 1
  let C_upper : ℝ := C_step / min α₀ β₀ + M / 2 + 1
  have hC_upper : 0 < C_upper := by
    have : 0 < min α₀ β₀ := lt_min hα₀ hβ₀
    positivity
  have hK₀_ge : M * C_shift ^ 2 / 2 ≤ m_min * K₀ := by
    have hK0_eq : m_min * K₀ = M * C_shift ^ 2 / 2 + m_min := by
      dsimp only [K₀]; field_simp [hm_min.ne']
    linarith only [hK0_eq, hm_min]
  refine ⟨ρ₀, C_upper, hρ₀, hC_upper, fun δ hδ => ?_⟩
  -- Step 1: Compact boundary gap so small (p₁, p₂, c) keeps maximizers inside ball y₀ (r/3) × ball z₀ (r/3)
  let Box : Set (Space n × Space n) := closedBall y₀ r ×ˢ closedBall z₀ r
  let InnerBox : Set (Space n × Space n) := ball y₀ (r / 3) ×ˢ ball z₀ (r / 3)
  let Bdy : Set (Space n × Space n) := Box \ InnerBox
  have hBox_comp : IsCompact Box := (isCompact_closedBall y₀ r).prod (isCompact_closedBall z₀ r)
  have hInner_open : IsOpen InnerBox := isOpen_ball.prod isOpen_ball
  have hBdy_comp : IsCompact Bdy := hBox_comp.diff hInner_open
  let H₀ : Space n × Space n → ℝ := fun q =>
    min (u₁ q.1) (v₁ q.2) - φ (t • q.1 + (1 - t) • q.2)
  have hH₀_cont : ContinuousOn H₀ Box := by
    have hcomb_cont : Continuous (fun q : Space n × Space n => t • q.1 + (1 - t) • q.2) :=
      (continuous_fst.const_smul t).add (continuous_snd.const_smul (1 - t))
    have hφ_comp : ContinuousOn (fun q : Space n × Space n => φ (t • q.1 + (1 - t) • q.2)) Box :=
      hφ.continuousOn.comp hcomb_cont.continuousOn
        (fun q hq => hsub (comb_mem_closedBall ht ht1 hq.1 hq.2))
    exact ((hu₁_cont.comp continuous_fst).min (hv₁_cont.comp continuous_snd)).continuousOn.sub hφ_comp
  have hgap : ∃ γ : ℝ, 0 < γ ∧ ∀ q ∈ Bdy, H₀ q ≤ H₀ (y₀, z₀) - γ := by
    by_cases hne : Bdy.Nonempty
    · obtain ⟨q, hqB, hqmax⟩ := hBdy_comp.exists_isMaxOn hne (hH₀_cont.mono sdiff_subset)
      have hqne : q ≠ (y₀, z₀) := by
        intro heq; subst heq
        exact hqB.2 ⟨mem_ball_self (by positivity), mem_ball_self (by positivity)⟩
      have hlt := hstrict q.1 hqB.1.1 q.2 hqB.1.2 hqne
      refine ⟨H₀ (y₀, z₀) - H₀ q, sub_pos.mpr hlt, fun w hw => ?_⟩
      have hle : H₀ w ≤ H₀ q := hqmax hw
      linarith
    · exact ⟨1, zero_lt_one, fun w hw => (hne ⟨w, hw⟩).elim⟩
  obtain ⟨γ, hγ, hBdy_bound⟩ := hgap
  let δ' : ℝ := min (min δ 1) (γ / (4 * R_box + 4))
  have hδ' : 0 < δ' := lt_min (lt_min hδ zero_lt_one) (by positivity)
  haveI : Nontrivial (Q n) := ⟨⟨0, WithLp.toLp 2 (0, (1 : ℝ)), fun h0 => by
    have := congrArg (fun q : Q n => (WithLp.ofLp q).2) h0
    simp at this⟩⟩
  let νQ : Measure ((Space n × Space n) × ℝ) :=
    ((volume : Measure (Space n)).prod (volume : Measure (Space n))).prod (volume : Measure ℝ)
  have hinv_prod : ∀ {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
      [Add A] [Add B] [MeasurableAdd₂ A] [MeasurableAdd₂ B]
      (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
      [μ.IsAddLeftInvariant] [ν.IsAddLeftInvariant], (μ.prod ν).IsAddLeftInvariant := by
    intro A B _ _ _ _ _ _ μ ν _ _ _ _
    refine ⟨fun g => ?_⟩
    have heq : (fun x : A × B => g + x) = Prod.map (fun a => g.1 + a) (fun b => g.2 + b) := rfl
    rw [heq, ← Measure.map_prod_map μ ν (measurable_const_add g.1) (measurable_const_add g.2),
      Measure.IsAddLeftInvariant.map_add_left_eq_self g.1,
      Measure.IsAddLeftInvariant.map_add_left_eq_self g.2]
  have _ : ((volume : Measure (Space n)).prod (volume : Measure (Space n))).IsAddLeftInvariant :=
    hinv_prod volume volume
  have _ : (((volume : Measure (Space n)).prod (volume : Measure (Space n))).prod (volume : Measure ℝ)).IsAddLeftInvariant :=
    hinv_prod _ volume
  have _ : νQ.IsAddHaarMeasure := by dsimp only [νQ]; exact ⟨⟩
  let eQ := tripleLpEquiv n
  let μQ : Measure (Q n) := Measure.map eQ νQ
  have : μQ.IsAddHaarMeasure := eQ.isAddHaarMeasure_map νQ
  -- Step 2: For any param ∈ ball (0 : Q n) δ', there is an interior equal-value maximizer
  have hex_contact (param : Q n) (hparam : param ∈ ball (0 : Q n) δ') :
      ∃ (y z : Space n) (α : ℝ),
        y ∈ ball y₀ (r / 3) ∧ z ∈ ball z₀ (r / 3) ∧
        α₀ ≤ α ∧ α ≤ 1 - β₀ ∧
        u₁ y + inner ℝ (qY param) y = v₁ z + inner ℝ (qZ param) z + qA param ∧
        (∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
          min (u₁ y' + inner ℝ (qY param) y') (v₁ z' + inner ℝ (qZ param) z' + qA param) -
            φ (t • y' + (1 - t) • z') ≤
          min (u₁ y + inner ℝ (qY param) y) (v₁ z + inner ℝ (qZ param) z + qA param) -
            φ (t • y + (1 - t) • z)) := by
    let p₁ := qY param; let p₂ := qZ param; let c := qA param
    have hp_norm : ‖param‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hparam
    have hp₁_lt : ‖p₁‖ < δ' := (hqY_le param).trans_lt hp_norm
    have hp₂_lt : ‖p₂‖ < δ' := (hqZ_le param).trans_lt hp_norm
    have hc_lt : |c| < δ' := by
      have h1 : ‖c‖ < δ' := (hqA_le param).trans_lt hp_norm
      rwa [Real.norm_eq_abs] at h1
    let Hp : Space n × Space n → ℝ := fun q =>
      min (u₁ q.1 + inner ℝ p₁ q.1) (v₁ q.2 + inner ℝ p₂ q.2 + c) - φ (t • q.1 + (1 - t) • q.2)
    have hHp_cont : ContinuousOn Hp Box := by
      have h1 : Continuous (fun q : Space n × Space n => u₁ q.1 + inner ℝ p₁ q.1) :=
        (hu₁_cont.comp continuous_fst).add (continuous_const.inner continuous_fst)
      have h2 : Continuous (fun q : Space n × Space n => v₁ q.2 + inner ℝ p₂ q.2 + c) :=
        ((hv₁_cont.comp continuous_snd).add (continuous_const.inner continuous_snd)).add continuous_const
      have hcomb_cont : Continuous (fun q : Space n × Space n => t • q.1 + (1 - t) • q.2) :=
        (continuous_fst.const_smul t).add (continuous_snd.const_smul (1 - t))
      have hφ_comp : ContinuousOn (fun q : Space n × Space n => φ (t • q.1 + (1 - t) • q.2)) Box :=
        hφ.continuousOn.comp hcomb_cont.continuousOn
          (fun q hq => hsub (comb_mem_closedBall ht ht1 hq.1 hq.2))
      exact (h1.min h2).continuousOn.sub hφ_comp
    have hBox_ne : Box.Nonempty := ⟨(y₀, z₀), mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
    obtain ⟨⟨y, z⟩, hyz_box, hyz_max⟩ := hBox_comp.exists_isMaxOn hBox_ne hHp_cont
    have hyz_inner : (y, z) ∈ InnerBox := by
      by_contra hnot
      have hB : (y, z) ∈ Bdy := ⟨hyz_box, hnot⟩
      have hgap_b := hBdy_bound (y, z) hB
      have hm : Hp (y₀, z₀) ≤ Hp (y, z) := hyz_max ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩
      have hdiff_pt (w : Space n × Space n) (hw : w ∈ Box) :
          |Hp w - H₀ w| ≤ δ' * (R_box + 1) := by
        have h1 : |inner ℝ p₁ w.1| ≤ δ' * R_box :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul hp₁_lt.le (hy_norm w.1 hw.1) (norm_nonneg _) hδ'.le)
        have h2 : |inner ℝ p₂ w.2 + c| ≤ δ' * (R_box + 1) := by
          calc |inner ℝ p₂ w.2 + c| ≤ |inner ℝ p₂ w.2| + |c| := abs_add_le _ _
            _ ≤ δ' * R_box + δ' := add_le_add
                ((abs_real_inner_le_norm _ _).trans (mul_le_mul hp₂_lt.le (hz_norm w.2 hw.2) (norm_nonneg _) hδ'.le))
                hc_lt.le
            _ = δ' * (R_box + 1) := by ring
        have hmin_diff : |min (u₁ w.1 + inner ℝ p₁ w.1) (v₁ w.2 + inner ℝ p₂ w.2 + c) -
            min (u₁ w.1) (v₁ w.2)| ≤ δ' * (R_box + 1) := by
          rw [abs_le]
          constructor
          · have hmin_l : min (u₁ w.1) (v₁ w.2) - δ' * (R_box + 1) ≤
                min (u₁ w.1 + inner ℝ p₁ w.1) (v₁ w.2 + inner ℝ p₂ w.2 + c) := by
              rw [← min_sub_sub_right]
              exact min_le_min (by linarith [(abs_le.mp h1).1, hδ']) (by linarith [(abs_le.mp h2).1])
            linarith
          · have hmin_r : min (u₁ w.1 + inner ℝ p₁ w.1) (v₁ w.2 + inner ℝ p₂ w.2 + c) ≤
                min (u₁ w.1) (v₁ w.2) + δ' * (R_box + 1) := by
              rw [← min_add_add_right]
              exact min_le_min (by linarith [(abs_le.mp h1).2, hδ']) (by linarith [(abs_le.mp h2).2])
            linarith
        have hsub_eq : Hp w - H₀ w =
            min (u₁ w.1 + inner ℝ p₁ w.1) (v₁ w.2 + inner ℝ p₂ w.2 + c) - min (u₁ w.1) (v₁ w.2) := by
          dsimp only [Hp, H₀]; ring
        rwa [hsub_eq]
      have hd1 := (abs_le.mp (hdiff_pt (y, z) hyz_box)).2
      have hd2 := (abs_le.mp (hdiff_pt (y₀, z₀) ⟨mem_closedBall_self hr.le, mem_closedBall_self hr.le⟩)).1
      have hsmall : 2 * (δ' * (R_box + 1)) < γ := by
        have hle : δ' ≤ γ / (4 * R_box + 4) := min_le_right _ _
        have hpos : (0 : ℝ) < 4 * R_box + 4 := by positivity
        calc 2 * (δ' * (R_box + 1)) ≤ 2 * ((γ / (4 * R_box + 4)) * (R_box + 1)) := by gcongr
          _ = γ / 2 := by field_simp [hpos.ne']; ring
          _ < γ := half_lt_self hγ
      linarith
    have heq_val : u₁ y + inner ℝ p₁ y = v₁ z + inner ℝ p₂ z + c := by
      by_contra hne_val
      have hcomb_in : t • y + (1 - t) • z ∈ closedBall x₀ (2 * r) :=
        comb_mem_closedBall ht ht1 hyz_box.1 hyz_box.2
      have hφ_diff : HasGradientAt φ (gradient φ (t • y + (1 - t) • z)) (t • y + (1 - t) • z) :=
        ((hφ.contDiffAt (hU.mem_nhds (hsub hcomb_in))).differentiableAt (by norm_num)).hasGradientAt
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · have hloc : IsLocalMax (fun z' => -φ (t • y + (1 - t) • z')) z := by
          have hcont_v : ContinuousAt (fun z' => v₁ z' + inner ℝ p₂ z' + c) z :=
            ((hv₁_cont.continuousAt).add (continuous_const.inner continuous_id).continuousAt).add continuousAt_const
          filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by linarith : r / 3 ≤ r) hyz_inner.2),
            hcont_v.eventually (eventually_gt_nhds hlt)] with z' hz' hz'gt
          have hm : Hp (y, z') ≤ Hp (y, z) := hyz_max ⟨hyz_box.1, ball_subset_closedBall hz'⟩
          dsimp only [Hp] at hm
          rw [min_eq_left hz'gt.le, min_eq_left hlt.le] at hm
          linarith
        have hfd : HasFDerivAt (fun z' => -φ (t • y + (1 - t) • z'))
            (-(1 - t) • toDual ℝ (Space n) (gradient φ (t • y + (1 - t) • z))) z := by
          have hlin : HasFDerivAt (fun z' : Space n => t • y + (1 - t) • z')
              ((1 - t) • ContinuousLinearMap.id ℝ (Space n)) z := by
            have h1 := (hasFDerivAt_const (t • y) z).add ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul (1 - t))
            exact h1.congr_fderiv (by ext w; simp)
          have hc := hφ_diff.hasFDerivAt.comp z hlin
          exact hc.neg.congr_fderiv (by ext w; simp; ring)
        have hzero := hloc.fderiv_eq_zero
        rw [hfd.fderiv] at hzero
        have hg0 : -(1 - t) • gradient φ (t • y + (1 - t) • z) = 0 :=
          (toDual ℝ (Space n)).injective (by simpa [map_smul] using hzero)
        exact hgrad_ne _ hcomb_in ((smul_eq_zero.mp hg0).resolve_left (neg_ne_zero.mpr ht_pos_1mt.ne'))
      · have hloc : IsLocalMax (fun y' => -φ (t • y' + (1 - t) • z)) y := by
          have hcont_u : ContinuousAt (fun y' => u₁ y' + inner ℝ p₁ y') y :=
            (hu₁_cont.continuousAt).add (continuous_const.inner continuous_id).continuousAt
          filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by linarith : r / 3 ≤ r) hyz_inner.1),
            hcont_u.eventually (eventually_gt_nhds hgt)] with y' hy' hy'gt
          have hm : Hp (y', z) ≤ Hp (y, z) := hyz_max ⟨ball_subset_closedBall hy', hyz_box.2⟩
          dsimp only [Hp] at hm
          rw [min_eq_right hy'gt.le, min_eq_right hgt.le] at hm
          linarith
        have hfd : HasFDerivAt (fun y' => -φ (t • y' + (1 - t) • z))
            ((-t) • toDual ℝ (Space n) (gradient φ (t • y + (1 - t) • z))) y := by
          have hlin : HasFDerivAt (fun y' : Space n => t • y' + (1 - t) • z)
              (t • ContinuousLinearMap.id ℝ (Space n)) y := by
            have h1 := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t).add (hasFDerivAt_const ((1 - t) • z) y)
            exact h1.congr_fderiv (by ext w; simp)
          have hc := hφ_diff.hasFDerivAt.comp y hlin
          exact hc.neg.congr_fderiv (by ext w; simp)
        have hzero := hloc.fderiv_eq_zero
        rw [hfd.fderiv] at hzero
        have hg0 : (-t) • gradient φ (t • y + (1 - t) • z) = 0 :=
          (toDual ℝ (Space n)).injective (by simpa [map_smul] using hzero)
        exact hgrad_ne _ hcomb_in ((smul_eq_zero.mp hg0).resolve_left (neg_ne_zero.mpr ht.ne'))
    obtain ⟨q₁, hq₁⟩ := exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₁_conv hf₁_lip y
    obtain ⟨q₂, hq₂⟩ := exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₂_conv hf₂_lip z
    have hmax' : ∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
        min (u₁ y' + inner ℝ p₁ y') (v₁ z' + inner ℝ p₂ z' + c) - φ (t • y' + (1 - t) • z') ≤
        min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) - φ (t • y + (1 - t) • z) := by
      intro y' hy' z' hz'
      have hm : Hp (y', z') ≤ Hp (y, z) := hyz_max ⟨hy', hz'⟩
      exact hm
    obtain ⟨α, hα_ge, hα_le, _, _⟩ :=
      envelope_first_order_subgradient_alignment ht ht1 hM hf₁_lip hf₂_lip hr hU hφ hsub hgrad_ne
        hC_max (by dsimp only [C_max]; linarith) le_rfl le_rfl hd_ge hyz_inner.1 hyz_inner.2
        (hy_norm y hyz_box.1) (hz_norm z hyz_box.2)
        (hp₁_lt.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (hp₂_lt.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
        heq_val hmax' hq₁ hq₂
    exact ⟨y, z, α, hyz_inner.1, hyz_inner.2, hα_ge, hα_le, heq_val, hmax'⟩
  -- Step 3: Contact set K_con ⊆ Q n and quadratic upper bound wrapper
  let K_con : Set (Q n) := {q | qY q ∈ ball y₀ (r / 3) ∧ qZ q ∈ ball z₀ (r / 3) ∧
    α₀ ≤ qA q ∧ qA q ≤ 1 - β₀ ∧
    ∃ param ∈ ball (0 : Q n) δ',
      u₁ (qY q) + inner ℝ (qY param) (qY q) = v₁ (qZ q) + inner ℝ (qZ param) (qZ q) + qA param ∧
      (∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
        min (u₁ y' + inner ℝ (qY param) y') (v₁ z' + inner ℝ (qZ param) z' + qA param) -
          φ (t • y' + (1 - t) • z') ≤
        min (u₁ (qY q) + inner ℝ (qY param) (qY q)) (v₁ (qZ q) + inner ℝ (qZ param) (qZ q) + qA param) -
          φ (t • qY q + (1 - t) • qZ q)) ∧
      (∀ q₁, IsSubgradient f₁ (qY q) q₁ →
        q₁ - M • qY q + qY param = (t / qA q) • gradient φ (t • qY q + (1 - t) • qZ q)) ∧
      (∀ q₂, IsSubgradient f₂ (qZ q) q₂ →
        q₂ - M • qZ q + qZ param = ((1 - t) / (1 - qA q)) • gradient φ (t • qY q + (1 - t) • qZ q))}
  have hC_step_nn : 0 ≤ C_step :=
    add_nonneg (add_nonneg (mul_nonneg hCφ.le (sq_nonneg _)) (mul_nonneg hd_max.le hK₀.le)) zero_le_one
  have hC_step_ge : Cφ * (1 + C_shift) ^ 2 + d_max * K₀ ≤ C_step := by dsimp only [C_step]; linarith only
  have hC_upper_ge : C_step / min α₀ β₀ + M / 2 ≤ C_upper := by dsimp only [C_upper]; linarith only
  have hquad_on_K : ∀ {y z : Space n} {α : ℝ} {p₁ p₂ : Space n} {c : ℝ},
      y ∈ ball y₀ (r / 3) → z ∈ ball z₀ (r / 3) → α₀ ≤ α → α ≤ 1 - β₀ →
      ‖p₁‖ < δ' → ‖p₂‖ < δ' →
      u₁ y + inner ℝ p₁ y = v₁ z + inner ℝ p₂ z + c →
      (∀ y' ∈ closedBall y₀ r, ∀ z' ∈ closedBall z₀ r,
        min (u₁ y' + inner ℝ p₁ y') (v₁ z' + inner ℝ p₂ z' + c) - φ (t • y' + (1 - t) • z') ≤
        min (u₁ y + inner ℝ p₁ y) (v₁ z + inner ℝ p₂ z + c) - φ (t • y + (1 - t) • z)) →
      (∀ q₁, IsSubgradient f₁ y q₁ → q₁ - M • y + p₁ = (t / α) • gradient φ (t • y + (1 - t) • z)) →
      (∀ q₂, IsSubgradient f₂ z q₂ → q₂ - M • z + p₂ = ((1 - t) / (1 - α)) • gradient φ (t • y + (1 - t) • z)) →
      (∀ q₁, IsSubgradient f₁ y q₁ → ∀ y' ∈ closedBall y ρ₀,
        f₁ y' - f₁ y ≤ inner ℝ q₁ (y' - y) + C_upper * ‖y' - y‖ ^ 2) ∧
      (∀ q₂, IsSubgradient f₂ z q₂ → ∀ z' ∈ closedBall z ρ₀,
        f₂ z' - f₂ z ≤ inner ℝ q₂ (z' - z) + C_upper * ‖z' - z‖ ^ 2) :=
    fun hy_in hz_in hα_ge hα_le hp₁_lt hp₂_lt heq_val hmax hq₁_eq hq₂_eq =>
      envelope_quadratic_upper_bound_on_contact ht ht1 hM hr hC_max (by dsimp only [C_max]; linarith)
        hα₀ hβ₀ hm_min (min_le_left _ _) (min_le_right _ _) hC_shift le_rfl hK₀ hK₀_ge
        (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_right _ _))
        hCφ hC_step_nn hC_step_ge hC_upper_ge
        hgrad_ne hd_ge hd_le hφ_quad hu₁_lip_box hv₁_lip_box
        hy_in hz_in hα_ge hα_le
        (hp₁_lt.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (hp₂_lt.le.trans ((min_le_left _ _).trans (min_le_right _ _)))
        heq_val hmax
        (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₁_conv hf₁_lip _)
        (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₂_conv hf₂_lip _)
        hq₁_eq hq₂_eq
  -- Step 4 & 5: Define the Lipschitz map Φ : K_con → Q n and prove ball 0 δ' ⊆ Φ '' K_con
  let Q1 (y : Space n) : Space n :=
    (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₁_conv hf₁_lip y).choose
  let Q2 (z : Space n) : Space n :=
    (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₂_conv hf₂_lip z).choose
  have hQ1 (y : Space n) : IsSubgradient f₁ y (Q1 y) :=
    (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₁_conv hf₁_lip y).choose_spec
  have hQ2 (z : Space n) : IsSubgradient f₂ z (Q2 z) :=
    (exists_isSubgradient_of_convex_lipschitz (volume : Measure (Space n)) hf₂_conv hf₂_lip z).choose_spec
  let Φ₁ (q : Q n) : Space n := (t / qA q) • gradient φ (t • qY q + (1 - t) • qZ q) + M • qY q - Q1 (qY q)
  let Φ₂ (q : Q n) : Space n := ((1 - t) / (1 - qA q)) • gradient φ (t • qY q + (1 - t) • qZ q) + M • qZ q - Q2 (qZ q)
  let Φ₃ (q : Q n) : ℝ := u₁ (qY q) - v₁ (qZ q) + inner ℝ (Φ₁ q) (qY q) - inner ℝ (Φ₂ q) (qZ q)
  let Φ (q : Q n) : Q n := WithLp.toLp 2 (WithLp.toLp 2 (Φ₁ q, Φ₂ q), Φ₃ q)
  have hball_sub : ball (0 : Q n) δ' ⊆ Φ '' K_con := by
    intro param hparam
    obtain ⟨y, z, α, hy_in, hz_in, _, _, heq_val, hmax⟩ := hex_contact param hparam
    have hp_norm : ‖param‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hparam
    have hp₁_le : ‖qY param‖ ≤ 1 :=
      ((hqY_le param).trans_lt hp_norm).le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hp₂_le : ‖qZ param‖ ≤ 1 :=
      ((hqZ_le param).trans_lt hp_norm).le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hy_cl : y ∈ closedBall y₀ r := ball_subset_closedBall (ball_subset_ball (by linarith only [hr]) hy_in)
    have hz_cl : z ∈ closedBall z₀ r := ball_subset_closedBall (ball_subset_ball (by linarith only [hr]) hz_in)
    have hx_in : t • y + (1 - t) • z ∈ closedBall x₀ (2 * r) :=
      comb_mem_closedBall ht ht1 hy_cl hz_cl
    have hfirst_any (q₁ q₂ : Space n) (hq₁ : IsSubgradient f₁ y q₁) (hq₂ : IsSubgradient f₂ z q₂) :
        ∃ α' : ℝ, α₀ ≤ α' ∧ α' ≤ 1 - β₀ ∧
          q₁ - M • y + qY param = (t / α') • gradient φ (t • y + (1 - t) • z) ∧
          q₂ - M • z + qZ param = ((1 - t) / (1 - α')) • gradient φ (t • y + (1 - t) • z) :=
      envelope_first_order_subgradient_alignment ht ht1 hM hf₁_lip hf₂_lip hr hU hφ hsub hgrad_ne
        hC_max (by dsimp only [C_max]; linarith) le_rfl le_rfl hd_ge hy_in hz_in
        (hy_norm y hy_cl) (hz_norm z hz_cl) hp₁_le hp₂_le heq_val hmax hq₁ hq₂
    obtain ⟨α', hα'_ge, hα'_le, hQ1_eq, hQ2_eq⟩ := hfirst_any (Q1 y) (Q2 z) (hQ1 y) (hQ2 z)
    have hall_q1 : ∀ q₁, IsSubgradient f₁ y q₁ →
        q₁ - M • y + qY param = (t / α') • gradient φ (t • y + (1 - t) • z) := by
      intro q₁ hq₁
      obtain ⟨α'', _, _, h1, h2⟩ := hfirst_any q₁ (Q2 z) hq₁ (hQ2 z)
      have heq_s : ((1 - t) / (1 - α'')) • gradient φ (t • y + (1 - t) • z) =
          ((1 - t) / (1 - α')) • gradient φ (t • y + (1 - t) • z) := h2.symm.trans hQ2_eq
      have hscalar : (1 - t) / (1 - α'') = (1 - t) / (1 - α') :=
        smul_left_injective ℝ (hgrad_ne _ hx_in) heq_s
      have hα_eq : α'' = α' := by
        have h1' : (1 - α'')⁻¹ = (1 - α')⁻¹ :=
          mul_left_cancel₀ ht_pos_1mt.ne' (by simpa only [div_eq_mul_inv] using hscalar)
        linarith [inv_injective h1']
      rwa [hα_eq] at h1
    have hall_q2 : ∀ q₂, IsSubgradient f₂ z q₂ →
        q₂ - M • z + qZ param = ((1 - t) / (1 - α')) • gradient φ (t • y + (1 - t) • z) := by
      intro q₂ hq₂
      obtain ⟨α'', _, _, h1, h2⟩ := hfirst_any (Q1 y) q₂ (hQ1 y) hq₂
      have heq_s : (t / α'') • gradient φ (t • y + (1 - t) • z) =
          (t / α') • gradient φ (t • y + (1 - t) • z) := h1.symm.trans hQ1_eq
      have hscalar : t / α'' = t / α' := smul_left_injective ℝ (hgrad_ne _ hx_in) heq_s
      have hα_eq : α'' = α' := by
        have h1' : α''⁻¹ = α'⁻¹ := mul_left_cancel₀ ht.ne' (by simpa only [div_eq_mul_inv] using hscalar)
        exact inv_injective h1'
      rwa [hα_eq] at h2
    let q' : Q n := WithLp.toLp 2 (WithLp.toLp 2 (y, z), α')
    refine ⟨q', ⟨hy_in, hz_in, hα'_ge, hα'_le, param, hparam, heq_val, hmax, hall_q1, hall_q2⟩, ?_⟩
    have hΦ1 : Φ₁ q' = qY param := by
      dsimp only [Φ₁, qY, qZ, qA, q']
      rw [← hQ1_eq]; abel
    have hΦ2 : Φ₂ q' = qZ param := by
      dsimp only [Φ₂, qY, qZ, qA, q']
      rw [← hQ2_eq]; abel
    have hΦ3 : Φ₃ q' = qA param := by
      dsimp only [Φ₃]; rw [hΦ1, hΦ2]; dsimp only [qY, qZ, q']
      linarith
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext hΦ1 hΦ2
    · exact hΦ3
  -- Step 6: Φ is LipschitzOnWith on K_con
  have hQ1_lip : ∃ L1 : ℝ≥0, LipschitzOnWith L1 Q1 (qY '' K_con) := by
    apply subgradient_lipschitzOn_of_quadratic_upper_bound hρ₀ hC_upper hf₁_lip (fun y _ => hQ1 y)
    rintro y ⟨q, hqK, rfl⟩ y' hy'
    obtain ⟨hy_in, hz_in, hα_ge, hα_le, param, hparam, heq_val, hmax, hq₁_eq, hq₂_eq⟩ := hqK
    have hp_norm : ‖param‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hparam
    exact (hquad_on_K hy_in hz_in hα_ge hα_le
      ((hqY_le param).trans_lt hp_norm) ((hqZ_le param).trans_lt hp_norm)
      heq_val hmax hq₁_eq hq₂_eq).1 (Q1 (qY q)) (hQ1 (qY q)) y' hy'
  have hQ2_lip : ∃ L2 : ℝ≥0, LipschitzOnWith L2 Q2 (qZ '' K_con) := by
    apply subgradient_lipschitzOn_of_quadratic_upper_bound hρ₀ hC_upper hf₂_lip (fun z _ => hQ2 z)
    rintro z ⟨q, hqK, rfl⟩ z' hz'
    obtain ⟨hy_in, hz_in, hα_ge, hα_le, param, hparam, heq_val, hmax, hq₁_eq, hq₂_eq⟩ := hqK
    have hp_norm : ‖param‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hparam
    exact (hquad_on_K hy_in hz_in hα_ge hα_le
      ((hqY_le param).trans_lt hp_norm) ((hqZ_le param).trans_lt hp_norm)
      heq_val hmax hq₁_eq hq₂_eq).2 (Q2 (qZ q)) (hQ2 (qZ q)) z' hz'
  obtain ⟨L1, hL1⟩ := hQ1_lip
  obtain ⟨L2, hL2⟩ := hQ2_lip
  have hΦ_lip : ∃ LΦ : ℝ≥0, LipschitzOnWith LΦ Φ K_con :=
    envelope_contact_map_lipschitzOn ht ht1 hM hr hα₀ hβ₀ hR_box hd_max hCφ
      hgrad_lip hd_le hy_norm hz_norm hu₁_lip_box hv₁_lip_box
      (fun y => (hQ1 y).norm_le hf₁_lip) (fun z => (hQ2 z).norm_le hf₂_lip)
      (fun q hq => ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩) hL1 hL2
  obtain ⟨LΦ, hLΦ⟩ := hΦ_lip
  -- Step 7: μQ K_con ≠ 0, so K_con intersects the full-measure set A_Q = {q | qY q ∈ A₁ ∧ qZ q ∈ A₂}
  have hK_ne_zero : μQ K_con ≠ 0 := by
    intro hKz
    have hΦz := addHaar_image_eq_zero_of_lipschitzOnWith μQ hLΦ hKz
    have hbz : μQ (ball (0 : Q n) δ') = 0 :=
      le_antisymm ((measure_mono hball_sub).trans hΦz.le) bot_le
    exact Measure.IsOpenPosMeasure.open_pos (ball (0 : Q n) δ') isOpen_ball (nonempty_ball.mpr hδ') hbz
  let A_Q : Set (Q n) := {q | qY q ∈ A₁ ∧ qZ q ∈ A₂}
  have hAQ_zero : μQ A_Qᶜ = 0 := by
    let N₁ := toMeasurable volume A₁ᶜ
    let N₂ := toMeasurable volume A₂ᶜ
    have hN₁m : MeasurableSet N₁ := measurableSet_toMeasurable volume A₁ᶜ
    have hN₂m : MeasurableSet N₂ := measurableSet_toMeasurable volume A₂ᶜ
    have hN₁z : volume N₁ = 0 := by rw [measure_toMeasurable]; exact hA₁
    have hN₂z : volume N₂ = 0 := by rw [measure_toMeasurable]; exact hA₂
    let S_prod : Set ((Space n × Space n) × ℝ) :=
      ((N₁ ×ˢ univ) ×ˢ univ) ∪ ((univ ×ˢ N₂) ×ˢ univ)
    let B : Set (Q n) := eQ '' S_prod
    have hsub_AQ : A_Qᶜ ⊆ B := by
      intro q hq
      refine ⟨((qY q, qZ q), qA q), ?_, rfl⟩
      by_cases h1 : qY q ∈ A₁
      · right; exact ⟨⟨mem_univ _, subset_toMeasurable volume A₂ᶜ (fun h2 => hq ⟨h1, h2⟩)⟩, mem_univ _⟩
      · left; exact ⟨⟨subset_toMeasurable volume A₁ᶜ h1, mem_univ _⟩, mem_univ _⟩
    have hSm : MeasurableSet S_prod :=
      ((hN₁m.prod MeasurableSet.univ).prod MeasurableSet.univ).union
        ((MeasurableSet.univ.prod hN₂m).prod MeasurableSet.univ)
    have hB_meas : MeasurableSet B := by
      have : B = eQ.symm ⁻¹' S_prod := by
        ext q; constructor
        · rintro ⟨w, hw, rfl⟩; simpa using hw
        · intro hq; exact ⟨eQ.symm q, hq, eQ.apply_symm_apply q⟩
      rw [this]; exact eQ.symm.continuous.measurable hSm
    have hBz : μQ B = 0 := by
      dsimp only [μQ, νQ]
      rw [Measure.map_apply eQ.continuous.measurable hB_meas, Set.preimage_image_eq _ eQ.injective]
      refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
      rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
        hN₁z, hN₂z, zero_mul, zero_mul, mul_zero, zero_mul, add_zero]
    exact le_antisymm ((measure_mono hsub_AQ).trans hBz.le) bot_le
  have hKA_ne : (K_con ∩ A_Q).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsub_K : K_con ⊆ A_Qᶜ := fun q hq hqA => by
      have : q ∈ K_con ∩ A_Q := ⟨hq, hqA⟩
      rw [hempty] at this; exact this
    exact hK_ne_zero (le_antisymm ((measure_mono hsub_K).trans hAQ_zero.le) bot_le)
  obtain ⟨q, hqK, hqA⟩ := hKA_ne
  obtain ⟨hy_in, hz_in, hα_ge, hα_le, param, hparam, heq_val, hmax, hq₁_eq, hq₂_eq⟩ := hqK
  have hp_norm : ‖param‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hparam
  have hδ'_le : δ' ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hp₁_lt : ‖qY param‖ < δ' := (hqY_le param).trans_lt hp_norm
  have hp₂_lt : ‖qZ param‖ < δ' := (hqZ_le param).trans_lt hp_norm
  have hc_lt : |qA param| < δ' := by
    have h1 : ‖qA param‖ < δ' := (hqA_le param).trans_lt hp_norm
    rwa [Real.norm_eq_abs] at h1
  obtain ⟨hup1, hup2⟩ := hquad_on_K hy_in hz_in hα_ge hα_le hp₁_lt hp₂_lt heq_val hmax hq₁_eq hq₂_eq
  exact ⟨qY param, qZ param, qA param, qY q, qZ q,
    hp₁_lt.trans_le hδ'_le, hp₂_lt.trans_le hδ'_le, hc_lt.trans_le hδ'_le,
    hy_in, hz_in, hqA.1, hqA.2, heq_val, hmax, hup1, hup2⟩

end EnvelopePerturbation
end BMCompactPDE
#print axioms BMCompactPDE.c2_quadratic_upper_bound
#print axioms BMCompactPDE.envelope_jensen_exists_good_maximizer
