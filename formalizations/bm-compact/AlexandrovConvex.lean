import LipschitzNull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Function.AEMeasurableSequence

/-! Alexandrov's theorem for globally convex, globally Lipschitz functions on a
finite-dimensional real inner product space, proved via Rademacher's theorem,
the Minty resolvent, and a telescoping subgradient estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal
namespace BMCompactPDE

/-- `f` has a second-order Taylor expansion at `x` with gradient `g` and
symmetric linear map `A : E →L[ℝ] E`. -/
def HasSecondOrderTaylorAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E) (A : E →L[ℝ] E) (x : E) : Prop :=
  (∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) ∧
  (fun y => f y - f x - inner ℝ g (y - x) - (1 / 2 : ℝ) * inner ℝ (A (y - x)) (y - x)) =o[𝓝 x]
    (fun y => ‖y - x‖ ^ 2)

/-- `p` is a subgradient of `f` at `x`. -/
def IsSubgradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x p : E) : Prop :=
  ∀ y, f x + inner ℝ p (y - x) ≤ f y

section Subgradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem IsSubgradient.norm_le {L : ℝ≥0} {f : E → ℝ} (hL : LipschitzWith L f)
    {x p : E} (hp : IsSubgradient f x p) : ‖p‖ ≤ L := by
  have h1 : f x + inner ℝ p ((x + p) - x) ≤ f (x + p) := hp (x + p)
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  have h2 : f (x + p) - f x ≤ (L : ℝ) * ‖p‖ := by
    calc f (x + p) - f x ≤ |f (x + p) - f x| := le_abs_self _
      _ = dist (f (x + p)) (f x) := (Real.dist_eq _ _).symm
      _ ≤ (L : ℝ) * dist (x + p) x := hL.dist_le_mul (x + p) x
      _ = (L : ℝ) * ‖p‖ := by simp [dist_eq_norm]
  have h3 : ‖p‖ ^ 2 ≤ (L : ℝ) * ‖p‖ := by linarith
  by_cases hp0 : ‖p‖ = 0
  · rw [hp0]; exact NNReal.coe_nonneg L
  · have hpos : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg p) (Ne.symm hp0)
    nlinarith

theorem IsSubgradient.of_hasFDerivAt [CompleteSpace E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {x : E} {D : E →L[ℝ] ℝ} (hD : HasFDerivAt f D x) :
    IsSubgradient f x ((toDual ℝ E).symm D) := by
  intro y
  have hlim : Tendsto (fun t : ℝ => (f (x + t • (y - x)) - f x) / t) (𝓝[>] 0)
      (𝓝 (D (y - x))) := by
    have hcomp : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (D (y - x)) 0 := by
      have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
      have hD' : HasFDerivAt f D (x + (0 : ℝ) • (y - x)) := by simpa using hD
      exact hD'.comp_hasDerivAt 0 hline
    have hd := hcomp.tendsto_slope_zero_right
    simpa [slope, smul_eq_mul, div_eq_inv_mul] using hd
  have hle : D (y - x) ≤ f y - f x := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have hconv := hf.2 (mem_univ x) (mem_univ y) (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    have hpt : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [hpt] at hconv
    simp only [smul_eq_mul] at hconv
    rw [div_le_iff₀ ht.1]
    linarith
  have hinner : inner ℝ ((toDual ℝ E).symm D) (y - x) = D (y - x) := by
    simp
  linarith

theorem IsSubgradient.eq_gradient [CompleteSpace E] {f : E → ℝ} {x p : E}
    (hp : IsSubgradient f x p) (hd : DifferentiableAt ℝ f x) :
    p = gradient f x := by
  have hle : ∀ v : E, inner ℝ p v ≤ inner ℝ (gradient f x) v := by
    intro v
    have hD : HasFDerivAt f (toDual ℝ E (gradient f x)) (x + (0 : ℝ) • v) := by
      simpa using hd.hasGradientAt.hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => f (x + t • v)) (inner ℝ (gradient f x) v) 0 := by
      have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have h := hD.comp_hasDerivAt 0 hline
      rwa [toDual_apply_apply] at h
    have hlim := hcomp.tendsto_slope_zero_right
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hsub := hp (x + t • v)
    rw [add_sub_cancel_left, real_inner_smul_right] at hsub
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [← div_eq_inv_mul, le_div_iff₀ ht]
    linarith
  have hzero : p - gradient f x = 0 := by
    have h1 := hle (p - gradient f x)
    have h2 : inner ℝ (p - gradient f x) (p - gradient f x) ≤ 0 := by
      rw [inner_sub_left]; linarith
    rw [real_inner_self_eq_norm_sq] at h2
    have h3 : ‖p - gradient f x‖ = 0 := by nlinarith [norm_nonneg (p - gradient f x)]
    exact norm_eq_zero.mp h3
  exact sub_eq_zero.mp hzero

end Subgradient

section Alexandrov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every globally convex, globally Lipschitz function on a finite-dimensional
real inner product space has a subgradient at every point. -/
theorem exists_isSubgradient_of_convex_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : ℝ≥0} {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) (y : E) :
    ∃ p : E, IsSubgradient f y p := by
  have hdense : Dense {x : E | DifferentiableAt ℝ f x} :=
    Measure.dense_of_ae (μ := μ) hL.ae_differentiableAt
  obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (hdense y)
  have hsub (k : ℕ) : IsSubgradient f (u k) (gradient f (u k)) :=
    IsSubgradient.of_hasFDerivAt hf (hu_mem k).hasFDerivAt
  have hmem (k : ℕ) : gradient f (u k) ∈ closedBall (0 : E) (L : ℝ) := by
    rw [mem_closedBall_zero_iff]
    exact (hsub k).norm_le hL
  obtain ⟨p, -, φ, hφ_mono, hp_lim⟩ :=
    (isCompact_closedBall (0 : E) (L : ℝ)).tendsto_subseq hmem
  refine ⟨p, fun w => ?_⟩
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 y) := hu_lim.comp hφ_mono.tendsto_atTop
  have hcont : Continuous f := hL.continuous
  have hlhs : Tendsto (fun k => f (u (φ k)) + inner ℝ (gradient f (u (φ k))) (w - u (φ k)))
      atTop (𝓝 (f y + inner ℝ p (w - y))) :=
    (hcont.continuousAt.tendsto.comp huφ).add
      (hp_lim.inner (tendsto_const_nhds.sub huφ))
  exact le_of_tendsto hlhs (Eventually.of_forall fun k => hsub (φ k) w)

/-- Existence of a Minty resolvent minimizer for a globally convex, globally
Lipschitz function. -/
theorem exists_minty_minimizer {L : ℝ≥0} {f : E → ℝ} (hL : LipschitzWith L f) (z : E) :
    ∃ x : E, ∀ y : E, f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤ f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
  let g : E → ℝ := fun y => f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2
  have hg_cont : Continuous g :=
    hL.continuous.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  let R : ℝ := 2 * (L : ℝ) + 1
  have hR : 0 < R := by positivity
  obtain ⟨x, -, hx_min⟩ :=
    (isCompact_closedBall z R).exists_isMinOn (nonempty_closedBall.mpr hR.le) hg_cont.continuousOn
  refine ⟨x, fun y => ?_⟩
  by_cases hy : y ∈ closedBall z R
  · exact hx_min hy
  · have hdist : R < ‖y - z‖ := by
      rw [mem_closedBall, dist_eq_norm] at hy
      exact lt_of_not_ge hy
    have hxz : g x ≤ g z := hx_min (mem_closedBall_self hR.le)
    have hlip : f z - f y ≤ (L : ℝ) * ‖y - z‖ := by
      calc f z - f y ≤ |f z - f y| := le_abs_self _
        _ = dist (f z) (f y) := (Real.dist_eq _ _).symm
        _ ≤ (L : ℝ) * dist z y := hL.dist_le_mul z y
        _ = (L : ℝ) * ‖y - z‖ := by rw [dist_comm, dist_eq_norm]
    have hzy : g z ≤ g y := by
      dsimp only [g]
      rw [sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero]
      nlinarith [norm_nonneg (y - z), NNReal.coe_nonneg L]
    exact hxz.trans hzy

/-- Minty resolvent `J(z) = argmin_x (f(x) + 1/2 ‖x - z‖²)`. -/
def mintyResolvent {L : ℝ≥0} {f : E → ℝ} (hL : LipschitzWith L f) (z : E) : E :=
  (exists_minty_minimizer hL z).choose

theorem mintyResolvent_isMin {L : ℝ≥0} {f : E → ℝ} (hL : LipschitzWith L f) (z y : E) :
    f (mintyResolvent hL z) + (1 / 2 : ℝ) * ‖mintyResolvent hL z - z‖ ^ 2 ≤
      f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 :=
  (exists_minty_minimizer hL z).choose_spec y

theorem mintyResolvent_subgradient {L : ℝ≥0} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) (z : E) :
    IsSubgradient f (mintyResolvent hL z) (z - mintyResolvent hL z) := by
  intro y
  set x := mintyResolvent hL z
  have hlim : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * t * ‖y - x‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * t * ‖y - x‖ ^ 2) (𝓝 0)
        (𝓝 ((1 / 2 : ℝ) * 0 * ‖y - x‖ ^ 2)) :=
      ((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun t : ℝ => f y - f x - inner ℝ (z - x) (y - x) + (1 / 2 : ℝ) * t * ‖y - x‖ ^ 2)
      (𝓝[>] 0) (𝓝 (f y - f x - inner ℝ (z - x) (y - x))) := by
    simpa using hlim.const_add (f y - f x - inner ℝ (z - x) (y - x))
  have hge : 0 ≤ f y - f x - inner ℝ (z - x) (y - x) := by
    apply ge_of_tendsto hlim'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    have hmin := mintyResolvent_isMin hL z ((1 - t) • x + t • y)
    have hconv := hf.2 (mem_univ x) (mem_univ y) (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    simp only [smul_eq_mul] at hconv
    have hvec : (1 - t) • x + t • y - z = (x - z) + t • (y - x) := by module
    rw [hvec, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.1.le] at hmin
    have hneg : inner ℝ (x - z) (y - x) = -inner ℝ (z - x) (y - x) := by
      rw [← inner_neg_left, neg_sub]
    rw [hneg] at hmin
    have hmul : 0 ≤ t * (f y - f x - inner ℝ (z - x) (y - x) + (1 / 2 : ℝ) * t * ‖y - x‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht.1
  linarith

theorem mintyResolvent_eq_of_subgradient {L : ℝ≥0} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) {x p : E}
    (hp : IsSubgradient f x p) : mintyResolvent hL (x + p) = x := by
  set w := mintyResolvent hL (x + p)
  have h1 := hp w
  have h2 : f w + inner ℝ (x + p - w) (x - w) ≤ f x :=
    mintyResolvent_subgradient hf hL (x + p) x
  have h2' : f w - inner ℝ (x + p - w) (w - x) ≤ f x := by
    rw [← neg_sub w x, inner_neg_right] at h2; linarith
  have h3 : inner ℝ (p - (x + p - w)) (w - x) ≤ 0 := by
    rw [inner_sub_left]; linarith
  have h4 : p - (x + p - w) = w - x := by abel
  rw [h4, real_inner_self_eq_norm_sq] at h3
  have h5 : ‖w - x‖ = 0 := by nlinarith [norm_nonneg (w - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

theorem mintyResolvent_lipschitzWith {L : ℝ≥0} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) :
    LipschitzWith 1 (mintyResolvent hL) := by
  refine LipschitzWith.of_dist_le_mul fun z₁ z₂ => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  set x₁ := mintyResolvent hL z₁
  set x₂ := mintyResolvent hL z₂
  have h1 : f x₁ + inner ℝ (z₁ - x₁) (x₂ - x₁) ≤ f x₂ :=
    mintyResolvent_subgradient hf hL z₁ x₂
  have h2 : f x₂ + inner ℝ (z₂ - x₂) (x₁ - x₂) ≤ f x₁ :=
    mintyResolvent_subgradient hf hL z₂ x₁
  have h1' : f x₁ - inner ℝ (z₁ - x₁) (x₁ - x₂) ≤ f x₂ := by
    rw [← neg_sub x₁ x₂, inner_neg_right] at h1; linarith
  have hmono : 0 ≤ inner ℝ ((z₁ - x₁) - (z₂ - x₂)) (x₁ - x₂) := by
    rw [inner_sub_left]; linarith
  have hvec : (z₁ - x₁) - (z₂ - x₂) = (z₁ - z₂) - (x₁ - x₂) := by abel
  rw [hvec, inner_sub_left, real_inner_self_eq_norm_sq] at hmono
  have hcs := real_inner_le_norm (z₁ - z₂) (x₁ - x₂)
  have hsq : ‖x₁ - x₂‖ ^ 2 ≤ ‖z₁ - z₂‖ * ‖x₁ - x₂‖ := by linarith
  by_cases h0 : ‖x₁ - x₂‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖x₁ - x₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- Continuity of the subdifferential at a point of differentiability. -/
theorem subgradient_tendsto_of_differentiableAt {L : ℝ≥0} {f : E → ℝ}
    (hL : LipschitzWith L f) {x : E} (hd : DifferentiableAt ℝ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball x δ, ∀ p : E, IsSubgradient f y p →
      ‖p - gradient f x‖ < ε := by
  by_contra hnot
  push_neg at hnot
  have hex (k : ℕ) : ∃ y ∈ ball x ((k : ℝ) + 1)⁻¹, ∃ p : E,
      IsSubgradient f y p ∧ ε ≤ ‖p - gradient f x‖ :=
    hnot ((k : ℝ) + 1)⁻¹ (by positivity)
  choose y hy p hp hge using hex
  have hy_lim : Tendsto y atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro r hr
    obtain ⟨N, hN⟩ := exists_nat_gt r⁻¹
    refine ⟨N, fun k hk => ?_⟩
    have h1 : dist (y k) x < ((k : ℝ) + 1)⁻¹ := mem_ball.mp (hy k)
    have h2 : ((k : ℝ) + 1)⁻¹ < r := by
      rw [inv_lt_comm₀ (by positivity) hr]
      have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    exact h1.trans h2
  have hp_mem (k : ℕ) : p k ∈ closedBall (0 : E) (L : ℝ) := by
    rw [mem_closedBall_zero_iff]; exact (hp k).norm_le hL
  obtain ⟨q, -, φ, hφ, hq_lim⟩ := (isCompact_closedBall (0 : E) (L : ℝ)).tendsto_subseq hp_mem
  have hsub_q : IsSubgradient f x q := by
    intro w
    have hyφ := hy_lim.comp hφ.tendsto_atTop
    have hlhs : Tendsto (fun k => f (y (φ k)) + inner ℝ (p (φ k)) (w - y (φ k)))
        atTop (𝓝 (f x + inner ℝ q (w - x))) :=
      (hL.continuous.continuousAt.tendsto.comp hyφ).add (hq_lim.inner (tendsto_const_nhds.sub hyφ))
    exact le_of_tendsto hlhs (Eventually.of_forall fun k => hp (φ k) w)
  have hqg : q = gradient f x := hsub_q.eq_gradient hd
  have hge_lim : ε ≤ ‖q - gradient f x‖ :=
    ge_of_tendsto ((hq_lim.sub tendsto_const_nhds).norm) (Eventually.of_forall fun k => hge (φ k))
  rw [hqg, sub_self, norm_zero] at hge_lim
  linarith

/-- First-order subgradient expansion from invertibility of `DJ(x + ∇f(x))`. -/
theorem subgradient_firstOrder_of_minty_invertible {L : ℝ≥0} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) {x : E}
    (hd : DifferentiableAt ℝ f x)
    {B Binv : E →L[ℝ] E} (hJ : HasFDerivAt (mintyResolvent hL) B (x + gradient f x))
    (hinv : Binv.comp B = ContinuousLinearMap.id ℝ E) :
    let M : E →L[ℝ] E := Binv - ContinuousLinearMap.id ℝ E
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball x δ, ∀ p : E, IsSubgradient f y p →
      ‖(p - gradient f x) - M (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro M ε hε
  set g := gradient f x
  let C : ℝ := ‖Binv‖ + 1
  have hC : 0 < C := by positivity
  let η : ℝ := min (1 / (2 * C)) (ε / (2 * C * (‖M‖ + 1)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hlo := hJ.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hr_bound⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  obtain ⟨δ₁, hδ₁, hsub_close⟩ := subgradient_tendsto_of_differentiableAt hL hd (half_pos hr)
  refine ⟨min δ₁ (r / 2), lt_min hδ₁ (half_pos hr), fun y hy p hp => ?_⟩
  have hy1 : y ∈ ball x δ₁ := ball_subset_ball (min_le_left _ _) hy
  have hy2 : ‖y - x‖ < r / 2 := by
    have := mem_ball.mp (ball_subset_ball (min_le_right _ _) hy)
    rwa [dist_eq_norm] at this
  have hpg : ‖p - g‖ < r / 2 := hsub_close y hy1 p hp
  have hz_dist : dist (y + p) (x + g) < r := by
    rw [dist_eq_norm, show (y + p) - (x + g) = (y - x) + (p - g) by abel]
    calc ‖(y - x) + (p - g)‖ ≤ ‖y - x‖ + ‖p - g‖ := norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hy2 hpg
      _ = r := add_halves r
  have hbound := hr_bound hz_dist
  have hJyp : mintyResolvent hL (y + p) = y := mintyResolvent_eq_of_subgradient hf hL hp
  have hJxg : mintyResolvent hL (x + g) = x := by
    have hg_sub : IsSubgradient f x g :=
      IsSubgradient.of_hasFDerivAt hf hd.hasFDerivAt
    exact mintyResolvent_eq_of_subgradient hf hL hg_sub
  rw [hJyp, hJxg] at hbound
  have hvec : (y + p) - (x + g) = (y - x) + (p - g) := by abel
  rw [hvec] at hbound
  have happly : Binv ((y - x) - B ((y - x) + (p - g))) = M (y - x) - (p - g) := by
    rw [map_sub]
    have hcomp : Binv (B ((y - x) + (p - g))) = (y - x) + (p - g) := by
      have := congrFun (congrArg DFunLike.coe hinv) ((y - x) + (p - g))
      simpa using this
    rw [hcomp]
    dsimp only [M]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  have herr : ‖(p - g) - M (y - x)‖ ≤ C * η * (‖y - x‖ + ‖p - g‖) := by
    rw [norm_sub_rev, ← happly]
    calc ‖Binv ((y - x) - B ((y - x) + (p - g)))‖
        ≤ ‖Binv‖ * ‖(y - x) - B ((y - x) + (p - g))‖ := Binv.le_opNorm _
      _ ≤ ‖Binv‖ * (η * ‖(y - x) + (p - g)‖) :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ ≤ C * (η * (‖y - x‖ + ‖p - g‖)) := by
          have h1 : ‖Binv‖ ≤ C := by dsimp only [C]; linarith
          have h2 : ‖(y - x) + (p - g)‖ ≤ ‖y - x‖ + ‖p - g‖ := norm_add_le _ _
          have h3 : 0 ≤ η * ‖(y - x) + (p - g)‖ := mul_nonneg hη.le (norm_nonneg _)
          have h4 : η * ‖(y - x) + (p - g)‖ ≤ η * (‖y - x‖ + ‖p - g‖) :=
            mul_le_mul_of_nonneg_left h2 hη.le
          exact (mul_le_mul_of_nonneg_right h1 h3).trans (mul_le_mul_of_nonneg_left h4 hC.le)
      _ = C * η * (‖y - x‖ + ‖p - g‖) := by ring
  have hCη1 : C * η ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * C) := min_le_left _ _
    calc C * η ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = 1 / 2 := by field_simp [hC.ne']
  have hCη2 : C * η * (2 * (‖M‖ + 1)) ≤ ε := by
    have h1 : η ≤ ε / (2 * C * (‖M‖ + 1)) := min_le_right _ _
    have hM1 : (0 : ℝ) < ‖M‖ + 1 := by positivity
    calc C * η * (2 * (‖M‖ + 1))
        ≤ C * (ε / (2 * C * (‖M‖ + 1))) * (2 * (‖M‖ + 1)) := by
          gcongr
      _ = ε := by field_simp [hC.ne', hM1.ne']
  have hpg_le : ‖p - g‖ ≤ ‖(p - g) - M (y - x)‖ + ‖M‖ * ‖y - x‖ := by
    calc ‖p - g‖ = ‖((p - g) - M (y - x)) + M (y - x)‖ := by congr 1; abel
      _ ≤ ‖(p - g) - M (y - x)‖ + ‖M (y - x)‖ := norm_add_le _ _
      _ ≤ ‖(p - g) - M (y - x)‖ + ‖M‖ * ‖y - x‖ := by gcongr; exact M.le_opNorm _
  have hpg_bound : ‖p - g‖ ≤ (2 * ‖M‖ + 1) * ‖y - x‖ := by
    have hsum : ‖y - x‖ + ‖p - g‖ ≥ 0 := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : ‖(p - g) - M (y - x)‖ ≤ (1 / 2 : ℝ) * (‖y - x‖ + ‖p - g‖) :=
      herr.trans (mul_le_mul_of_nonneg_right hCη1 hsum)
    linarith
  have htotal : ‖y - x‖ + ‖p - g‖ ≤ 2 * (‖M‖ + 1) * ‖y - x‖ := by linarith
  calc ‖(p - g) - M (y - x)‖
      ≤ C * η * (‖y - x‖ + ‖p - g‖) := herr
    _ ≤ C * η * (2 * (‖M‖ + 1) * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left htotal (mul_nonneg hC.le hη.le)
    _ = C * η * (2 * (‖M‖ + 1)) * ‖y - x‖ := by ring
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hCη2 (norm_nonneg _)

/-- Telescoping subgradient estimate: a first-order subgradient expansion gives
a second-order Taylor expansion with the symmetrized linear map. -/
theorem hasSecondOrderTaylorAt_of_subgradient_firstOrder
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : ℝ≥0} {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    {x : E} {g : E} {M : E →L[ℝ] E}
    (hfirst : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball x δ, ∀ p : E, IsSubgradient f y p →
      ‖(p - g) - M (y - x)‖ ≤ ε * ‖y - x‖) :
    HasSecondOrderTaylorAt f g ((1 / 2 : ℝ) • (M + M.adjoint)) x := by
  let A : E →L[ℝ] E := (1 / 2 : ℝ) • (M + M.adjoint)
  have hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro u v
    dsimp only [A]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      RCLike.conj_to_real, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  have hquad (v : E) : inner ℝ (A v) v = inner ℝ (M v) v := by
    dsimp only [A]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      inner_smul_left, inner_add_left, RCLike.conj_to_real,
      ContinuousLinearMap.adjoint_inner_left]
    rw [real_inner_comm v (M v)]
    ring
  refine ⟨hsymm, ?_⟩
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hfirst ε hε
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  set v := y - x
  have hv_lt : ‖v‖ < δ := by simpa [dist_eq_norm, v] using mem_ball.mp hy
  rw [hquad v, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg ‖v‖)]
  have hseg (N : ℕ) (hN : 0 < N) :
      inner ℝ g v + (((N : ℝ) - 1) / (2 * (N : ℝ))) * inner ℝ (M v) v - ε * ‖v‖ ^ 2 ≤
        f y - f x ∧
      f y - f x ≤
        inner ℝ g v + (((N : ℝ) + 1) / (2 * (N : ℝ))) * inner ℝ (M v) v + ε * ‖v‖ ^ 2 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    let pt : ℕ → E := fun k => x + ((k : ℝ) / (N : ℝ)) • v
    let p : ℕ → E := fun k => (exists_isSubgradient_of_convex_lipschitz μ hf hL (pt k)).choose
    have hp_sub (k : ℕ) : IsSubgradient f (pt k) (p k) :=
      (exists_isSubgradient_of_convex_lipschitz μ hf hL (pt k)).choose_spec
    have hpt_ball (k : ℕ) (hk : k ≤ N) : pt k ∈ ball x δ := by
      rw [mem_ball, dist_eq_norm]
      have hdiff : pt k - x = ((k : ℝ) / (N : ℝ)) • v := by dsimp only [pt]; abel
      rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hfrac : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNpos).mpr (by exact_mod_cast hk)
      calc ((k : ℝ) / (N : ℝ)) * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hfrac (norm_nonneg _)
        _ = ‖v‖ := one_mul _
        _ < δ := hv_lt
    have herr (k : ℕ) (hk : k ≤ N) :
        |inner ℝ (p k - g) v - ((k : ℝ) / (N : ℝ)) * inner ℝ (M v) v| ≤ ε * ‖v‖ ^ 2 := by
      have hb := hbound (pt k) (hpt_ball k hk) (p k) (hp_sub k)
      have hdiff : pt k - x = ((k : ℝ) / (N : ℝ)) • v := by dsimp only [pt]; abel
      rw [hdiff, map_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at hb
      have hfrac : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNpos).mpr (by exact_mod_cast hk)
      have h1 : inner ℝ (p k - g) v - ((k : ℝ) / (N : ℝ)) * inner ℝ (M v) v =
          inner ℝ ((p k - g) - ((k : ℝ) / (N : ℝ)) • M v) v := by
        rw [inner_sub_left, inner_sub_left, inner_sub_left, real_inner_smul_left]
      rw [h1]
      calc |inner ℝ ((p k - g) - ((k : ℝ) / (N : ℝ)) • M v) v|
          ≤ ‖(p k - g) - ((k : ℝ) / (N : ℝ)) • M v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (ε * (((k : ℝ) / (N : ℝ)) * ‖v‖)) * ‖v‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ ≤ (ε * (1 * ‖v‖)) * ‖v‖ := by gcongr
        _ = ε * ‖v‖ ^ 2 := by ring
    have hstep_lo (k : ℕ) : (1 / (N : ℝ)) * inner ℝ (p k) v ≤ f (pt (k + 1)) - f (pt k) := by
      have hsub := hp_sub k (pt (k + 1))
      have hd : pt (k + 1) - pt k = (1 / (N : ℝ)) • v := by
        dsimp only [pt]
        have h1 : (((k + 1 : ℕ) : ℝ) / (N : ℝ)) - ((k : ℝ) / (N : ℝ)) = 1 / (N : ℝ) := by
          push_cast; field_simp [hNpos.ne']; ring
        rw [show (x + (((k + 1 : ℕ) : ℝ) / (N : ℝ)) • v) - (x + ((k : ℝ) / (N : ℝ)) • v) =
            ((((k + 1 : ℕ) : ℝ) / (N : ℝ)) - ((k : ℝ) / (N : ℝ))) • v by module, h1]
      rw [hd, real_inner_smul_right] at hsub
      linarith
    have hstep_hi (k : ℕ) : f (pt (k + 1)) - f (pt k) ≤ (1 / (N : ℝ)) * inner ℝ (p (k + 1)) v := by
      have hsub := hp_sub (k + 1) (pt k)
      have hd : pt k - pt (k + 1) = -(1 / (N : ℝ)) • v := by
        dsimp only [pt]
        have h1 : ((k : ℝ) / (N : ℝ)) - (((k + 1 : ℕ) : ℝ) / (N : ℝ)) = -(1 / (N : ℝ)) := by
          push_cast; field_simp [hNpos.ne']; ring
        rw [show (x + ((k : ℝ) / (N : ℝ)) • v) - (x + (((k + 1 : ℕ) : ℝ) / (N : ℝ)) • v) =
            (((k : ℝ) / (N : ℝ)) - (((k + 1 : ℕ) : ℝ) / (N : ℝ))) • v by module, h1, neg_smul]
      rw [hd, neg_smul, inner_neg_right, real_inner_smul_right] at hsub
      linarith
    have htele : ∑ k ∈ Finset.range N, (f (pt (k + 1)) - f (pt k)) = f y - f x := by
      rw [Finset.sum_range_sub (fun k => f (pt k)) N]
      have hptN : pt N = y := by
        dsimp only [pt, v]; rw [div_self hNpos.ne', one_smul, add_sub_cancel]
      have hpt0 : pt 0 = x := by
        dsimp only [pt]; simp
      rw [hptN, hpt0]
    have hsum_k : (∑ k ∈ Finset.range N, (k : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
      have hnat := Finset.sum_range_id N
      have hcast : (2 : ℝ) * ∑ k ∈ Finset.range N, (k : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
        have h2 : 2 * ∑ k ∈ Finset.range N, k = N * (N - 1) := by
          rw [hnat, Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd]
        have h2R : (2 : ℝ) * (∑ k ∈ Finset.range N, k : ℕ) = ((N * (N - 1) : ℕ) : ℝ) := by
          exact_mod_cast h2
        rw [Nat.cast_sum] at h2R
        rw [h2R, Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hN), Nat.cast_one]
      linarith
    have hsum_k1 : (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
      have : (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range N, (k : ℝ)) + (N : ℝ) := by
        simp [Finset.sum_add_distrib]
      rw [this, hsum_k]; ring
    constructor
    · calc inner ℝ g v + (((N : ℝ) - 1) / (2 * (N : ℝ))) * inner ℝ (M v) v - ε * ‖v‖ ^ 2
          = (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
              (inner ℝ g v + ((k : ℝ) / (N : ℝ)) * inner ℝ (M v) v - ε * ‖v‖ ^ 2) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul, ← Finset.sum_div, ← Finset.sum_mul, hsum_k]
            field_simp [hNpos.ne']
        _ ≤ (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, inner ℝ (p k) v := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro k hk
            have hk_le : k ≤ N := (Finset.mem_range.mp hk).le
            have he := (abs_le.mp (herr k hk_le)).1
            rw [inner_sub_left] at he
            linarith
        _ = ∑ k ∈ Finset.range N, (1 / (N : ℝ)) * inner ℝ (p k) v := by
            rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ Finset.range N, (f (pt (k + 1)) - f (pt k)) :=
            Finset.sum_le_sum fun k _ => hstep_lo k
        _ = f y - f x := htele
    · calc f y - f x
          = ∑ k ∈ Finset.range N, (f (pt (k + 1)) - f (pt k)) := htele.symm
        _ ≤ ∑ k ∈ Finset.range N, (1 / (N : ℝ)) * inner ℝ (p (k + 1)) v :=
            Finset.sum_le_sum fun k _ => hstep_hi k
        _ = (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, inner ℝ (p (k + 1)) v := by
            rw [Finset.mul_sum]
        _ ≤ (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
              (inner ℝ g v + (((k + 1 : ℕ) : ℝ) / (N : ℝ)) * inner ℝ (M v) v + ε * ‖v‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum
            intro k hk
            have hk_le : k + 1 ≤ N := Finset.mem_range.mp hk
            have he := (abs_le.mp (herr (k + 1) hk_le)).2
            rw [inner_sub_left] at he
            linarith
        _ = inner ℝ g v + (((N : ℝ) + 1) / (2 * (N : ℝ))) * inner ℝ (M v) v + ε * ‖v‖ ^ 2 := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, ← Finset.sum_div, ← Finset.sum_mul, hsum_k1]
            field_simp [hNpos.ne']
  have hlim_lo : Tendsto (fun N : ℕ => (((N : ℝ) - 1) / (2 * (N : ℝ)))) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h1 : ∀ᶠ N : ℕ in atTop, (((N : ℝ) - 1) / (2 * (N : ℝ))) = 1 / 2 - (2 * (N : ℝ))⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hN']
    rw [tendsto_congr' h1]
    have hinv : Tendsto (fun N : ℕ => (2 * (N : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    simpa using tendsto_const_nhds.sub hinv
  have hlim_hi : Tendsto (fun N : ℕ => (((N : ℝ) + 1) / (2 * (N : ℝ)))) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h1 : ∀ᶠ N : ℕ in atTop, (((N : ℝ) + 1) / (2 * (N : ℝ))) = 1 / 2 + (2 * (N : ℝ))⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hN']
    rw [tendsto_congr' h1]
    have hinv : Tendsto (fun N : ℕ => (2 * (N : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    simpa using tendsto_const_nhds.add hinv
  have hlo_all : inner ℝ g v + (1 / 2 : ℝ) * inner ℝ (M v) v - ε * ‖v‖ ^ 2 ≤ f y - f x :=
    le_of_tendsto ((tendsto_const_nhds.add (hlim_lo.mul_const _)).sub tendsto_const_nhds)
      (by filter_upwards [eventually_gt_atTop 0] with N hN; exact (hseg N hN).1)
  have hhi_all : f y - f x ≤ inner ℝ g v + (1 / 2 : ℝ) * inner ℝ (M v) v + ε * ‖v‖ ^ 2 :=
    ge_of_tendsto ((tendsto_const_nhds.add (hlim_hi.mul_const _)).add tendsto_const_nhds)
      (by filter_upwards [eventually_gt_atTop 0] with N hN; exact (hseg N hN).2)
  rw [abs_le]
  constructor <;> linarith

/-- **Alexandrov's theorem** for globally convex, globally Lipschitz functions
on a finite-dimensional real inner product space: almost every point admits a
second-order Taylor expansion with symmetric Hessian. -/
theorem alexandrov_convex_lipschitz [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : ℝ≥0} {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x ∧ ∃ A : E →L[ℝ] E,
      HasSecondOrderTaylorAt f (gradient f x) A x := by
  let J := mintyResolvent hL
  have hJlip : LipschitzWith 1 J := mintyResolvent_lipschitzWith hf hL
  have hJdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ J z := hJlip.ae_differentiableAt
  let N₁ : Set E := toMeasurable μ {z | ¬ DifferentiableAt ℝ J z}
  have hN₁_meas : MeasurableSet N₁ := measurableSet_toMeasurable μ _
  have hN₁_zero : μ N₁ = 0 := by
    rw [measure_toMeasurable]
    exact hJdiff
  have hJ_N₁_zero : μ (J '' N₁) = 0 :=
    addHaar_image_eq_zero_of_lipschitzWith μ hJlip hN₁_zero
  let S₀ : Set E := N₁ᶜ ∩ {z | (fderiv ℝ J z).det = 0}
  have hS₀_meas : MeasurableSet S₀ := by
    apply hN₁_meas.compl.inter
    have hmf : Measurable (fderiv ℝ J) := measurable_fderiv ℝ J
    exact (ContinuousLinearMap.continuous_det.measurable.comp hmf) (measurableSet_singleton 0)
  have hJ_S₀_zero : μ (J '' S₀) = 0 := by
    refine le_antisymm ?_ bot_le
    have hle := addHaar_image_le_lintegral_abs_det_fderiv μ hS₀_meas (f := J) (f' := fderiv ℝ J)
      (fun z hz => by
        have hd : DifferentiableAt ℝ J z := by
          by_contra hnot
          exact hz.1 (subset_toMeasurable μ _ hnot)
        exact hd.hasFDerivAt.hasFDerivWithinAt)
    have hzero : (∫⁻ z in S₀, ENNReal.ofReal |(fderiv ℝ J z).det| ∂μ) = 0 := by
      calc (∫⁻ z in S₀, ENNReal.ofReal |(fderiv ℝ J z).det| ∂μ)
          = ∫⁻ _ in S₀, (0 : ℝ≥0∞) ∂μ :=
            setLIntegral_congr_fun hS₀_meas (fun z hz => by
              have h0 : (fderiv ℝ J z).det = 0 := hz.2
              rw [h0]; simp)
        _ = 0 := lintegral_zero
    exact hle.trans hzero.le
  have hae_not_N₁ : ∀ᵐ x ∂μ, x ∉ J '' N₁ := by
    rw [ae_iff]
    convert hJ_N₁_zero using 2
    ext a; simp
  have hae_not_S₀ : ∀ᵐ x ∂μ, x ∉ J '' S₀ := by
    rw [ae_iff]
    convert hJ_S₀_zero using 2
    ext a; simp
  filter_upwards [hL.ae_differentiableAt, hae_not_N₁, hae_not_S₀] with x hfx hx1 hx2
  refine ⟨hfx, ?_⟩
  let z := x + gradient f x
  have hJz : J z = x := by
    have hg_sub : IsSubgradient f x (gradient f x) :=
      IsSubgradient.of_hasFDerivAt hf hfx.hasFDerivAt
    exact mintyResolvent_eq_of_subgradient hf hL hg_sub
  have hz_not_N₁ : z ∉ N₁ := fun hz => hx1 ⟨z, hz, hJz⟩
  have hJdz : DifferentiableAt ℝ J z := by
    by_contra hnot
    exact hz_not_N₁ (subset_toMeasurable μ _ hnot)
  have hdet_ne : (fderiv ℝ J z).det ≠ 0 := fun h0 => hx2 ⟨z, ⟨hz_not_N₁, h0⟩, hJz⟩
  let B : E →L[ℝ] E := fderiv ℝ J z
  let b := Module.finBasis ℝ E
  have hunit : IsUnit (LinearMap.toMatrix b b B.toLinearMap).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.mpr hdet_ne
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofIsUnitDet hunit
  let Binv : E →L[ℝ] E := e.symm.toLinearMap.toContinuousLinearMap
  have hinv : Binv.comp B = ContinuousLinearMap.id ℝ E := by
    ext v
    change e.symm (e v) = v
    exact e.symm_apply_apply v
  exact ⟨(1 / 2 : ℝ) • ((Binv - ContinuousLinearMap.id ℝ E) +
      (Binv - ContinuousLinearMap.id ℝ E).adjoint),
    hasSecondOrderTaylorAt_of_subgradient_firstOrder μ hf hL
      (subgradient_firstOrder_of_minty_invertible hf hL hfx hJdz.hasFDerivAt hinv)⟩

end Alexandrov
end BMCompactPDE
#print axioms BMCompactPDE.HasSecondOrderTaylorAt
#print axioms BMCompactPDE.alexandrov_convex_lipschitz
