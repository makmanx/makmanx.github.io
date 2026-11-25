import TaylorViscosity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! Two finite-dimensional calculus helpers for JLM comparison:
1. Any `C²` function on a finite-dimensional inner product space is semiconvex
   and Lipschitz on any closed ball.
2. Uniform continuity of `g ↦ ‖g‖^(p-2) * matrixNormalizedPLaplacian p g A`
   near a nonzero gradient `g₀` over all operators `‖A‖ ≤ K`. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff NNReal BigOperators
namespace BMCompactPDE

section C2Semiconvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Any `C²` function `ψ` on `E` satisfies that `-ψ + (C/2)‖·‖²` is convex and
Lipschitz on any closed ball `closedBall z₀ r`. -/
theorem c2_neg_semiconvex_on_closedBall {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (z₀ : E) {r : ℝ} (hr : 0 < r) :
    ∃ (C : ℝ) (L : ℝ≥0), 0 < C ∧
      ConvexOn ℝ (closedBall z₀ r) (fun z => -ψ z + (C / 2) * ‖z‖ ^ 2) ∧
      LipschitzOnWith L (fun z => -ψ z + (C / 2) * ‖z‖ ^ 2) (closedBall z₀ r) := by
  have hcomp : IsCompact (closedBall z₀ r) := isCompact_closedBall z₀ r
  have hne : (closedBall z₀ r).Nonempty := nonempty_closedBall.mpr hr.le
  have h2norm : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ ψ) z‖) :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).norm
  obtain ⟨z₁, -, hz₁⟩ := hcomp.exists_isMaxOn hne h2norm.continuousOn
  let C : ℝ := ‖fderiv ℝ (fderiv ℝ ψ) z₁‖ + 1
  have hC : 0 < C := by positivity
  have hCbound : ∀ z ∈ closedBall z₀ r, ‖fderiv ℝ (fderiv ℝ ψ) z‖ ≤ C := fun z hz => by
    have hle : ‖fderiv ℝ (fderiv ℝ ψ) z‖ ≤ ‖fderiv ℝ (fderiv ℝ ψ) z₁‖ := hz₁ hz
    dsimp only [C]; linarith
  let g : E → ℝ := fun z => -ψ z + (C / 2) * ‖z‖ ^ 2
  have hg_c2 : ContDiff ℝ 2 g :=
    hψ.neg.add (contDiff_const.mul (contDiff_id.norm_sq ℝ))
  have hg_fderiv (z : E) : HasFDerivAt g (-fderiv ℝ ψ z + C • toDual ℝ E z) z := by
    have h1 : HasFDerivAt (fun w => -ψ w) (-fderiv ℝ ψ z) z :=
      (hψ.differentiable (by norm_num) z).hasFDerivAt.neg
    have h2 : HasFDerivAt (fun w : E => (C / 2) * ‖w‖ ^ 2) (C • toDual ℝ E z) z := by
      have hsq : HasFDerivAt (fun w : E => ‖w‖ ^ 2) ((2 : ℝ) • toDual ℝ E z) z := by
        have hi : HasFDerivAt (fun w : E => inner ℝ w w)
            ((2 : ℝ) • toDual ℝ E z) z := by
          refine ((hasFDerivAt_id z).inner ℝ (hasFDerivAt_id z)).congr_fderiv ?_
          ext v; simp [toDual_apply_apply, real_inner_comm]; ring
        simpa only [real_inner_self_eq_norm_sq] using hi
      refine (hsq.const_mul (C / 2)).congr_fderiv ?_
      ext v; simp; ring
    exact h1.add h2
  have hg_conv : ConvexOn ℝ (closedBall z₀ r) g := by
    refine ⟨convex_closedBall z₀ r, fun x hx y hy a b ha hb hab => ?_⟩
    by_cases hxy : x = y
    · subst hxy
      have : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
      rw [this]; simp only [smul_eq_mul]
      have hmul : a * g x + b * g x = g x := by rw [← add_mul, hab, one_mul]
      linarith
    · let v : E := y - x
      let φ : ℝ → ℝ := fun t => g (x + t • v)
      have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x
      have hφ1 (t : ℝ) : HasDerivAt φ (-fderiv ℝ ψ (x + t • v) v + C * inner ℝ (x + t • v) v) t := by
        have h := (hg_fderiv (x + t • v)).comp_hasDerivAt t (hline t)
        simpa only [φ, Function.comp_def, add_apply, neg_apply, smul_apply,
          toDual_apply_apply, smul_eq_mul] using h
      have hφ2 (t : ℝ) : HasDerivAt (fun s : ℝ => -fderiv ℝ ψ (x + s • v) v + C * inner ℝ (x + s • v) v)
          (-(fderiv ℝ (fderiv ℝ ψ) (x + t • v) v) v + C * ‖v‖ ^ 2) t := by
        have hd1 : HasFDerivAt (fun z => fderiv ℝ ψ z) (fderiv ℝ (fderiv ℝ ψ) (x + t • v)) (x + t • v) :=
          ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (x + t • v)).hasFDerivAt
        have hd2 : HasDerivAt (fun s : ℝ => fderiv ℝ ψ (x + s • v))
            (fderiv ℝ (fderiv ℝ ψ) (x + t • v) v) t :=
          hd1.comp_hasDerivAt t (hline t)
        have hd3 : HasDerivAt (fun s : ℝ => -fderiv ℝ ψ (x + s • v) v)
            (-(fderiv ℝ (fderiv ℝ ψ) (x + t • v) v) v) t := by
          have := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt t hd2
          exact this.neg
        have hd4 : HasDerivAt (fun s : ℝ => C * inner ℝ (x + s • v) v) (C * ‖v‖ ^ 2) t := by
          have hi : HasDerivAt (fun s : ℝ => inner ℝ (x + s • v) v) (‖v‖ ^ 2) t := by
            have := (hline t).inner ℝ (hasDerivAt_const t v)
            simpa only [inner_zero_right, zero_add, real_inner_self_eq_norm_sq] using this
          exact hi.const_mul C
        exact hd3.add hd4
      have hφ_conv : ConvexOn ℝ (Icc (0 : ℝ) 1) φ := by
        apply convexOn_of_deriv2_nonneg (convex_Icc 0 1)
        · exact (hg_c2.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
        · exact fun t _ => (hφ1 t).differentiableAt.differentiableWithinAt
        · exact fun t _ => (by
            have heq : deriv φ = fun s => -fderiv ℝ ψ (x + s • v) v + C * inner ℝ (x + s • v) v :=
              funext fun s => (hφ1 s).deriv
            rw [heq]; exact (hφ2 t).differentiableAt.differentiableWithinAt)
        · intro t ht
          have heq : deriv φ = fun s => -fderiv ℝ ψ (x + s • v) v + C * inner ℝ (x + s • v) v :=
            funext fun s => (hφ1 s).deriv
          change 0 ≤ deriv (deriv φ) t
          rw [heq, (hφ2 t).deriv]
          have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
          have hmem : x + t • v ∈ closedBall z₀ r := by
            have hpt : x + t • v = (1 - t) • x + t • y := by dsimp only [v]; module
            rw [hpt]
            exact (convex_closedBall z₀ r) hx hy (sub_nonneg.mpr ht'.2) ht'.1 (by ring)
          have hbn : ‖(fderiv ℝ (fderiv ℝ ψ) (x + t • v) v) v‖ ≤ C * ‖v‖ ^ 2 := by
            calc ‖(fderiv ℝ (fderiv ℝ ψ) (x + t • v) v) v‖
                ≤ ‖fderiv ℝ (fderiv ℝ ψ) (x + t • v) v‖ * ‖v‖ :=
                  (fderiv ℝ (fderiv ℝ ψ) (x + t • v) v).le_opNorm v
              _ ≤ (‖fderiv ℝ (fderiv ℝ ψ) (x + t • v)‖ * ‖v‖) * ‖v‖ :=
                  mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ ψ) (x + t • v)).le_opNorm v) (norm_nonneg _)
              _ = ‖fderiv ℝ (fderiv ℝ ψ) (x + t • v)‖ * ‖v‖ ^ 2 := by ring
              _ ≤ C * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right (hCbound _ hmem) (sq_nonneg _)
          rw [Real.norm_eq_abs] at hbn
          linarith [(abs_le.mp hbn).2]
      have hconv_b := hφ_conv.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) ha hb hab
      have hpt0 : φ 0 = g x := by simp [φ]
      have hpt1 : φ 1 = g y := by simp [φ, v]
      have hptb : φ (a * 0 + b * 1) = g (a • x + b • y) := by
        dsimp only [φ, v]
        congr 1
        have ha' : a = 1 - b := by linarith
        rw [ha']; module
      simp only [smul_eq_mul] at hconv_b ⊢
      rw [hpt0, hpt1, hptb] at hconv_b
      exact hconv_b
  have h1cont : Continuous (fun z => fderiv ℝ g z) := hg_c2.continuous_fderiv (by norm_num)
  obtain ⟨z₂, -, hz₂⟩ := hcomp.exists_isMaxOn hne h1cont.norm.continuousOn
  let L : ℝ≥0 := ⟨‖fderiv ℝ g z₂‖ + 1, by positivity⟩
  have hg_lip : LipschitzOnWith L g (closedBall z₀ r) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => (hg_fderiv z).differentiableAt)
    · intro z hz
      have hle : ‖fderiv ℝ g z‖ ≤ ‖fderiv ℝ g z₂‖ := hz₂ hz
      change ‖fderiv ℝ g z‖ ≤ ‖fderiv ℝ g z₂‖ + 1
      linarith
    · exact convex_closedBall z₀ r
  exact ⟨C, L, hC, hg_conv, hg_lip⟩

end C2Semiconvex

section UniformContinuity
variable {n : ℕ}

/-- Uniform continuity of `g ↦ ‖g‖^(p-2) * matrixNormalizedPLaplacian p g A`
near a nonzero gradient `g₀`, uniformly over all `A` with `‖A‖ ≤ K`. -/
theorem matrixClassicalPLaplacian_uniform_close {p K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    {g₀ : Space n} (hg₀ : g₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g₁ ∈ ball g₀ δ, ∀ g₂ ∈ ball g₀ δ,
      g₁ ≠ 0 ∧ g₂ ≠ 0 ∧ ∀ A : Space n →L[ℝ] Space n, ‖A‖ ≤ K →
        |‖g₁‖ ^ (p - 2) * matrixNormalizedPLaplacian p g₁ A -
          ‖g₂‖ ^ (p - 2) * matrixNormalizedPLaplacian p g₂ A| < ε := by
  have hg₀_pos : 0 < ‖g₀‖ := norm_pos_iff.mpr hg₀
  -- Bound |trace A| ≤ n * K
  have htrace_bound (A : Space n →L[ℝ] Space n) (hA : ‖A‖ ≤ K) :
      |LinearMap.trace ℝ (Space n) A.toLinearMap| ≤ (n : ℝ) * K := by
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
    calc |∑ i : Fin n, (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap) i i|
        ≤ ∑ i : Fin n, |(LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap) i i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, K := by
          apply Finset.sum_le_sum
          intro i _
          rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
            b.repr_apply_apply, real_inner_comm]
          calc |inner ℝ (A (b i)) (b i)|
              ≤ ‖A (b i)‖ * ‖b i‖ := abs_real_inner_le_norm _ _
            _ ≤ (‖A‖ * ‖b i‖) * ‖b i‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
            _ = ‖A‖ := by rw [b.orthonormal.1 i]; ring
            _ ≤ K := hA
      _ = (n : ℝ) * K := by simp
  -- Continuity of α(g) = ‖g‖^(p-2) and β(g) = (p-2) * ‖g‖^(p-4) at g₀
  have hα_cont : ContinuousAt (fun g : Space n => ‖g‖ ^ (p - 2)) g₀ :=
    continuous_norm.continuousAt.rpow_const (Or.inl hg₀_pos.ne')
  have hβ_cont : ContinuousAt (fun g : Space n => (p - 2) * ‖g‖ ^ (p - 4)) g₀ :=
    continuousAt_const.mul (continuous_norm.continuousAt.rpow_const (Or.inl hg₀_pos.ne'))
  have hM_bound : ∃ M : ℝ, 0 < M ∧ ∀ g ∈ ball g₀ (‖g₀‖ / 2),
      |(p - 2) * ‖g‖ ^ (p - 4)| ≤ M ∧ ‖g‖ ≤ 2 * ‖g₀‖ := by
    have hcomp := isCompact_closedBall g₀ (‖g₀‖ / 2)
    have hcont_on : ContinuousOn (fun g : Space n => |(p - 2) * ‖g‖ ^ (p - 4)|)
        (closedBall g₀ (‖g₀‖ / 2)) := by
      refine (continuousOn_const.mul ?_).abs
      refine ContinuousOn.rpow_const continuous_norm.continuousOn fun g hg => Or.inl ?_
      have hdist : ‖g - g₀‖ ≤ ‖g₀‖ / 2 := by simpa [mem_closedBall, dist_eq_norm] using hg
      have hge : ‖g₀‖ / 2 ≤ ‖g‖ := by
        have := norm_sub_norm_le g₀ g
        rw [norm_sub_rev] at this
        linarith
      linarith
    obtain ⟨gₘ, -, hgₘ⟩ := hcomp.exists_isMaxOn (nonempty_closedBall.mpr (by positivity)) hcont_on
    refine ⟨|(p - 2) * ‖gₘ‖ ^ (p - 4)| + 1, by positivity, fun g hg => ?_⟩
    have hcl := ball_subset_closedBall hg
    have h1 : |(p - 2) * ‖g‖ ^ (p - 4)| ≤ |(p - 2) * ‖gₘ‖ ^ (p - 4)| := hgₘ hcl
    have hdist : ‖g - g₀‖ < ‖g₀‖ / 2 := by simpa [mem_ball, dist_eq_norm] using hg
    have h2 : ‖g‖ ≤ 2 * ‖g₀‖ := by
      have := norm_add_le (g - g₀) g₀
      rw [sub_add_cancel] at this
      linarith
    exact ⟨by linarith, h2⟩
  obtain ⟨M, hMpos, hM⟩ := hM_bound
  let C₁ : ℝ := (n : ℝ) * K + 1
  let C₂ : ℝ := K * (2 * ‖g₀‖) ^ 2 + 1
  let C₃ : ℝ := M * K * (4 * ‖g₀‖) + 1
  have hC₁ : 0 < C₁ := by positivity
  have hC₂ : 0 < C₂ := by positivity
  have hC₃ : 0 < C₃ := by positivity
  obtain ⟨δ₁, hδ₁, hα_close⟩ := Metric.continuousAt_iff.mp hα_cont (ε / (6 * C₁)) (by positivity)
  obtain ⟨δ₂, hδ₂, hβ_close⟩ := Metric.continuousAt_iff.mp hβ_cont (ε / (6 * C₂)) (by positivity)
  let δ : ℝ := min (min (‖g₀‖ / 2) (ε / (6 * C₃))) (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min (lt_min (half_pos hg₀_pos) (by positivity)) (lt_min hδ₁ hδ₂)
  refine ⟨δ, hδ, fun g₁ hg₁ g₂ hg₂ => ?_⟩
  have hne_of {g : Space n} (hg : g ∈ ball g₀ δ) : g ≠ 0 := by
    have h1 : ‖g - g₀‖ < ‖g₀‖ / 2 := by
      have := mem_ball.mp hg
      rw [dist_eq_norm] at this
      exact this.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    intro h0; subst h0; rw [zero_sub, norm_neg] at h1; linarith
  have hg₁_ne : g₁ ≠ 0 := hne_of hg₁
  have hg₂_ne : g₂ ≠ 0 := hne_of hg₂
  refine ⟨hg₁_ne, hg₂_ne, fun A hA => ?_⟩
  have hrew (g : Space n) (hg : g ≠ 0) :
      ‖g‖ ^ (p - 2) * matrixNormalizedPLaplacian p g A =
        ‖g‖ ^ (p - 2) * LinearMap.trace ℝ (Space n) A.toLinearMap +
        ((p - 2) * ‖g‖ ^ (p - 4)) * inner ℝ (A g) g := by
    unfold matrixNormalizedPLaplacian
    rw [mul_add]
    congr 1
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hrpow : ‖g‖ ^ (p - 2) * (‖g‖ ^ 2)⁻¹ = ‖g‖ ^ (p - 4) := by
      rw [show (‖g‖ ^ 2)⁻¹ = ‖g‖ ^ (-2 : ℝ) by
        rw [Real.rpow_neg hgpos.le, Real.rpow_two],
        ← Real.rpow_add hgpos, show p - 2 + -2 = p - 4 by ring]
    calc ‖g‖ ^ (p - 2) * ((p - 2) * (‖g‖ ^ 2)⁻¹ * inner ℝ (A g) g)
        = (p - 2) * (‖g‖ ^ (p - 2) * (‖g‖ ^ 2)⁻¹) * inner ℝ (A g) g := by ring
      _ = ((p - 2) * ‖g‖ ^ (p - 4)) * inner ℝ (A g) g := by rw [hrpow]
  rw [hrew g₁ hg₁_ne, hrew g₂ hg₂_ne]
  have hg₁_half : g₁ ∈ ball g₀ (‖g₀‖ / 2) := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hg₁
  have hg₂_half : g₂ ∈ ball g₀ (‖g₀‖ / 2) := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hg₂
  have hα_diff : |‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)| < ε / (3 * C₁) := by
    have h1 := hα_close (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hg₁)
    have h2 := hα_close (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hg₂)
    rw [Real.dist_eq] at h1 h2
    calc |‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)|
        = |(‖g₁‖ ^ (p - 2) - ‖g₀‖ ^ (p - 2)) - (‖g₂‖ ^ (p - 2) - ‖g₀‖ ^ (p - 2))| := by ring_nf
      _ ≤ |‖g₁‖ ^ (p - 2) - ‖g₀‖ ^ (p - 2)| + |‖g₂‖ ^ (p - 2) - ‖g₀‖ ^ (p - 2)| := abs_sub _ _
      _ < ε / (6 * C₁) + ε / (6 * C₁) := add_lt_add h1 h2
      _ = ε / (3 * C₁) := by ring
  have hβ_diff : |(p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)| < ε / (3 * C₂) := by
    have h1 := hβ_close (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hg₁)
    have h2 := hβ_close (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hg₂)
    rw [Real.dist_eq] at h1 h2
    calc |(p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)|
        = |((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₀‖ ^ (p - 4)) -
            ((p - 2) * ‖g₂‖ ^ (p - 4) - (p - 2) * ‖g₀‖ ^ (p - 4))| := by ring_nf
      _ ≤ |(p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₀‖ ^ (p - 4)| +
          |(p - 2) * ‖g₂‖ ^ (p - 4) - (p - 2) * ‖g₀‖ ^ (p - 4)| := abs_sub _ _
      _ < ε / (6 * C₂) + ε / (6 * C₂) := add_lt_add h1 h2
      _ = ε / (3 * C₂) := by ring
  have hg12_dist : ‖g₁ - g₂‖ < ε / (3 * C₃) := by
    have h1 : ‖g₁ - g₀‖ < ε / (6 * C₃) := by
      have := mem_ball.mp hg₁; rw [dist_eq_norm] at this
      exact this.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h2 : ‖g₂ - g₀‖ < ε / (6 * C₃) := by
      have := mem_ball.mp hg₂; rw [dist_eq_norm] at this
      exact this.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    calc ‖g₁ - g₂‖ = ‖(g₁ - g₀) - (g₂ - g₀)‖ := by congr 1; abel
      _ ≤ ‖g₁ - g₀‖ + ‖g₂ - g₀‖ := norm_sub_le _ _
      _ < ε / (6 * C₃) + ε / (6 * C₃) := add_lt_add h1 h2
      _ = ε / (3 * C₃) := by ring
  have hterm1 : |(‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)) * LinearMap.trace ℝ (Space n) A.toLinearMap| < ε / 3 := by
    rw [abs_mul]
    have htr := htrace_bound A hA
    have htr_lt : |LinearMap.trace ℝ (Space n) A.toLinearMap| ≤ C₁ := by dsimp only [C₁]; linarith
    calc |‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)| * |LinearMap.trace ℝ (Space n) A.toLinearMap|
        ≤ |‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)| * C₁ := mul_le_mul_of_nonneg_left htr_lt (abs_nonneg _)
      _ < (ε / (3 * C₁)) * C₁ := mul_lt_mul_of_pos_right hα_diff hC₁
      _ = ε / 3 := by field_simp [hC₁.ne']
  have hquad1 : |inner ℝ (A g₁) g₁| ≤ C₂ := by
    calc |inner ℝ (A g₁) g₁|
        ≤ ‖A g₁‖ * ‖g₁‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖g₁‖) * ‖g₁‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ ≤ (K * (2 * ‖g₀‖)) * (2 * ‖g₀‖) := by gcongr; exact (hM g₁ hg₁_half).2; exact (hM g₁ hg₁_half).2
      _ ≤ C₂ := by dsimp only [C₂]; nlinarith
  have hterm2 : |((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)) * inner ℝ (A g₁) g₁| < ε / 3 := by
    rw [abs_mul]
    calc |(p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)| * |inner ℝ (A g₁) g₁|
        ≤ |(p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)| * C₂ :=
          mul_le_mul_of_nonneg_left hquad1 (abs_nonneg _)
      _ < (ε / (3 * C₂)) * C₂ := mul_lt_mul_of_pos_right hβ_diff hC₂
      _ = ε / 3 := by field_simp [hC₂.ne']
  have hquad_diff : |inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂| ≤ K * (4 * ‖g₀‖) * ‖g₁ - g₂‖ := by
    have hdecomp : inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂ =
        inner ℝ (A (g₁ - g₂)) g₁ + inner ℝ (A g₂) (g₁ - g₂) := by
      rw [map_sub, inner_sub_left, inner_sub_right]; ring
    rw [hdecomp]
    have h1 : |inner ℝ (A (g₁ - g₂)) g₁| ≤ K * (2 * ‖g₀‖) * ‖g₁ - g₂‖ := by
      calc |inner ℝ (A (g₁ - g₂)) g₁|
          ≤ ‖A (g₁ - g₂)‖ * ‖g₁‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖g₁ - g₂‖) * ‖g₁‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ (K * ‖g₁ - g₂‖) * (2 * ‖g₀‖) := by gcongr; exact (hM g₁ hg₁_half).2
        _ = K * (2 * ‖g₀‖) * ‖g₁ - g₂‖ := by ring
    have h2 : |inner ℝ (A g₂) (g₁ - g₂)| ≤ K * (2 * ‖g₀‖) * ‖g₁ - g₂‖ := by
      calc |inner ℝ (A g₂) (g₁ - g₂)|
          ≤ ‖A g₂‖ * ‖g₁ - g₂‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖g₂‖) * ‖g₁ - g₂‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ (K * (2 * ‖g₀‖)) * ‖g₁ - g₂‖ := by gcongr; exact (hM g₂ hg₂_half).2
    calc |inner ℝ (A (g₁ - g₂)) g₁ + inner ℝ (A g₂) (g₁ - g₂)|
        ≤ |inner ℝ (A (g₁ - g₂)) g₁| + |inner ℝ (A g₂) (g₁ - g₂)| := abs_add_le _ _
      _ ≤ K * (2 * ‖g₀‖) * ‖g₁ - g₂‖ + K * (2 * ‖g₀‖) * ‖g₁ - g₂‖ := add_le_add h1 h2
      _ = K * (4 * ‖g₀‖) * ‖g₁ - g₂‖ := by ring
  have hterm3 : |((p - 2) * ‖g₂‖ ^ (p - 4)) * (inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂)| < ε / 3 := by
    rw [abs_mul]
    have hβ2 : |(p - 2) * ‖g₂‖ ^ (p - 4)| ≤ M := (hM g₂ hg₂_half).1
    have hle1 : |(p - 2) * ‖g₂‖ ^ (p - 4)| * |inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂| ≤
        M * (K * (4 * ‖g₀‖) * ‖g₁ - g₂‖) :=
      mul_le_mul hβ2 hquad_diff (abs_nonneg _) hMpos.le
    have hle2 : M * (K * (4 * ‖g₀‖) * ‖g₁ - g₂‖) ≤ C₃ * ‖g₁ - g₂‖ := by
      have : M * K * (4 * ‖g₀‖) ≤ C₃ := by dsimp only [C₃]; linarith
      nlinarith [norm_nonneg (g₁ - g₂)]
    calc |(p - 2) * ‖g₂‖ ^ (p - 4)| * |inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂|
        ≤ C₃ * ‖g₁ - g₂‖ := hle1.trans hle2
      _ < C₃ * (ε / (3 * C₃)) := mul_lt_mul_of_pos_left hg12_dist hC₃
      _ = ε / 3 := by field_simp [hC₃.ne']
  have htotal : (‖g₁‖ ^ (p - 2) * LinearMap.trace ℝ (Space n) A.toLinearMap +
        (p - 2) * ‖g₁‖ ^ (p - 4) * inner ℝ (A g₁) g₁) -
      (‖g₂‖ ^ (p - 2) * LinearMap.trace ℝ (Space n) A.toLinearMap +
        (p - 2) * ‖g₂‖ ^ (p - 4) * inner ℝ (A g₂) g₂) =
      (‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)) * LinearMap.trace ℝ (Space n) A.toLinearMap +
      ((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)) * inner ℝ (A g₁) g₁ +
      ((p - 2) * ‖g₂‖ ^ (p - 4)) * (inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂) := by ring
  rw [htotal]
  calc |(‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)) * LinearMap.trace ℝ (Space n) A.toLinearMap +
        ((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)) * inner ℝ (A g₁) g₁ +
        ((p - 2) * ‖g₂‖ ^ (p - 4)) * (inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂)|
      ≤ |(‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)) * LinearMap.trace ℝ (Space n) A.toLinearMap +
        ((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)) * inner ℝ (A g₁) g₁| +
        |((p - 2) * ‖g₂‖ ^ (p - 4)) * (inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂)| := abs_add_le _ _
    _ ≤ |(‖g₁‖ ^ (p - 2) - ‖g₂‖ ^ (p - 2)) * LinearMap.trace ℝ (Space n) A.toLinearMap| +
        |((p - 2) * ‖g₁‖ ^ (p - 4) - (p - 2) * ‖g₂‖ ^ (p - 4)) * inner ℝ (A g₁) g₁| +
        |((p - 2) * ‖g₂‖ ^ (p - 4)) * (inner ℝ (A g₁) g₁ - inner ℝ (A g₂) g₂)| := by
          gcongr; exact abs_add_le _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

end UniformContinuity
end BMCompactPDE
#print axioms BMCompactPDE.c2_neg_semiconvex_on_closedBall
#print axioms BMCompactPDE.matrixClassicalPLaplacian_uniform_close
