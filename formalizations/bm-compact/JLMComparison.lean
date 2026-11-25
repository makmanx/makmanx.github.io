import JensenLemma
import C2Semiconvex
import RootDoublingCompact
import UpstreamSelectedDirichlet
import RootForcedRegularization

/-! General Juutinen–Lindqvist–Manfredi (JLM) viscosity comparison (manuscript
Lemma 3.7) for all `1 < p < ∞` and all dimensions `n ≥ 2`, without any `C¹` or
`C²` regularity assumptions on the viscosity subsolution or the weak harmonic
comparator. Proved via sup/inf-convolution, Alexandrov's theorem, local Jensen's
lemma, and positive-source approximation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter Metric MeasureTheory InnerProductSpace Bornology
open scoped Topology ContDiff ENNReal NNReal
namespace BMCompactPDE

section ForcedConvergenceAllP

private theorem jlm_energy_eq_lp_power
    {n : ℕ} {p : ℝ} (hp : 1 < p) {μ : Measure (Space n)}
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x, ‖g x‖ ^ p ∂μ) = ‖hg.toLp g‖ ^ p := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he := integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun v => ‖v‖ ^ p))
  exact he.symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral
    (zero_lt_one.trans hp) (hg.toLp g)).symm

/-- Strong `W^{1,p}` convergence of vanishing-source Dirichlet perturbations of
an actual weak `p`-harmonic pair, valid for ALL `1 < p < ∞` and `2 ≤ n`. -/
theorem WeakPHarmonicPair.forced_family_W1p_tendsto_allp_gen
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPHarmonicPair p Ω f gf) (hf : SobolevPair p Ω f gf)
    (hn : 2 ≤ n) (hΩb : IsBounded Ω)
    {c : ℕ → ℝ} {w : ℕ → Space n → ℝ} {gw : ℕ → Space n → Space n}
    (hw : ∀ j, ZeroBoundarySobolevPair p Ω (w j) (gw j))
    (hu : ∀ j, WeakPSourcePair p (c j) Ω (f + w j) (gf + gw j))
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
    Tendsto (fun j => eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hp0 : 0 < p := zero_lt_one.trans hf.1
  let μ := volume.restrict Ω
  let F := hf.2.2.1.toLp gf
  let G (j : ℕ) := (hw j).1.2.2.1.toLp (gw j)
  let A (j : ℕ) := F + G j
  have hupper (j : ℕ) : ‖A j‖ ^ p ≤ ‖F‖ ^ p + p * c j * (∫ x in Ω, w j x) := by
    have htest := (hw j).smul_actual (-1)
    have hmin := (hu j).energy_tangent_global hΩb (hf.add (hw j).1) htest
    have hvec : ∀ x, (gf + gw j) x + ((-1 : ℝ) • gw j) x = gf x := fun x => by
      simp only [Pi.add_apply, Pi.smul_apply, neg_one_smul]; abel
    simp_rw [hvec] at hmin
    have hneg : (∫ x in Ω, ((-1 : ℝ) • w j) x) = -(∫ x in Ω, w j x) := by
      simp only [Pi.smul_apply, neg_one_smul, integral_neg]
    rw [hneg] at hmin
    rw [jlm_energy_eq_lp_power hf.1 (hf.2.2.1.add (hw j).1.2.2.1),
      jlm_energy_eq_lp_power hf.1 hf.2.2.1,
      MemLp.toLp_add hf.2.2.1 (hw j).1.2.2.1] at hmin
    linarith
  have hmid (j : ℕ) : ‖F‖ ^ p ≤ ‖(1 / 2 : ℝ) • (A j + F)‖ ^ p := by
    have hm := hH.source_zero.energy_tangent_global hΩb hf ((hw j).smul_actual (1 / 2 : ℝ))
    simp only [mul_zero, zero_mul, add_zero] at hm
    change (∫ x in Ω, ‖gf x‖ ^ p) ≤ ∫ x in Ω, ‖(gf + (1 / 2 : ℝ) • gw j) x‖ ^ p at hm
    rw [jlm_energy_eq_lp_power hf.1 hf.2.2.1,
      jlm_energy_eq_lp_power hf.1 (hf.2.2.1.add ((hw j).1.2.2.1.const_smul (1 / 2 : ℝ))),
      MemLp.toLp_add hf.2.2.1 ((hw j).1.2.2.1.const_smul (1 / 2 : ℝ)),
      MemLp.toLp_const_smul (1 / 2 : ℝ) (hw j).1.2.2.1] at hm
    have hvec : F + (1 / 2 : ℝ) • G j = (1 / 2 : ℝ) • (A j + F) := by dsimp only [A]; module
    dsimp only [F, G, A] at hvec ⊢
    simpa only [hvec] using hm
  obtain ⟨K, hK, hload⟩ := exists_W0_source_load_bound_allp hf.1 hn hΩb
  obtain ⟨C₀, hC₀, hcbound⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ j, |c j| ≤ C₀ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc 1 zero_lt_one
    let C₁ : ℝ := 1 + ∑ j ∈ Finset.range N, |c j|
    refine ⟨C₁, by positivity, fun j => ?_⟩
    by_cases hj : j < N
    · have hle : |c j| ≤ ∑ i ∈ Finset.range N, |c i| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_range.mpr hj)
      dsimp only [C₁]; linarith
    · have h1 := hN j (Nat.le_of_not_lt hj)
      rw [Real.dist_eq, sub_zero] at h1
      have hsum : 0 ≤ ∑ i ∈ Finset.range N, |c i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
      dsimp only [C₁]; linarith
  let L : ℝ := C₀ * K
  have hL : 0 ≤ L := mul_nonneg hC₀ hK
  let M : ℝ := ‖F‖ ^ p / p + L * ‖F‖
  obtain ⟨Q, _, hQ⟩ := source_energy_coercive_allp hf.1 hL M
  have hAbound (j : ℕ) : ‖A j‖ ≤ Q := by
    have hG : ‖G j‖ ≤ ‖A j‖ + ‖F‖ := by
      calc ‖G j‖ = ‖A j - F‖ := by congr 1; dsimp only [A]; abel
        _ ≤ ‖A j‖ + ‖F‖ := norm_sub_le _ _
    have hl : |∫ x in Ω, w j x| ≤ K * ‖G j‖ := by
      simpa only [G, Lp.norm_toLp] using hload (hw j)
    have hcj : c j * (∫ x in Ω, w j x) ≤ L * (‖A j‖ + ‖F‖) := by
      calc c j * (∫ x in Ω, w j x)
          ≤ |c j * (∫ x in Ω, w j x)| := le_abs_self _
        _ = |c j| * |∫ x in Ω, w j x| := abs_mul _ _
        _ ≤ C₀ * (K * ‖G j‖) := mul_le_mul (hcbound j) hl (abs_nonneg _) hC₀
        _ = L * ‖G j‖ := by dsimp only [L]; ring
        _ ≤ L * (‖A j‖ + ‖F‖) := mul_le_mul_of_nonneg_left hG hL
    have he := hupper j
    have henergy : ‖A j‖ ^ p / p - L * ‖A j‖ ≤ M := by
      apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀ hp0).mpr
      dsimp only [M]
      have hid : (‖F‖ ^ p / p + L * ‖F‖ + L * ‖A j‖) * p = ‖F‖ ^ p + p * (L * (‖A j‖ + ‖F‖)) := by
        field_simp [hp0.ne']; ring
      rw [hid]
      nlinarith [he, hcj, hp0]
    by_contra hnot
    exact (not_lt_of_ge henergy) (hQ ‖A j‖ (le_of_not_ge hnot))
  have hload_bound (j : ℕ) : |∫ x in Ω, w j x| ≤ K * (Q + ‖F‖) := by
    have hG : ‖G j‖ ≤ Q + ‖F‖ := by
      calc ‖G j‖ = ‖A j - F‖ := by congr 1; dsimp only [A]; abel
        _ ≤ ‖A j‖ + ‖F‖ := norm_sub_le _ _
        _ ≤ Q + ‖F‖ := by linarith [hAbound j]
    have hl : |∫ x in Ω, w j x| ≤ K * ‖G j‖ := by
      simpa only [G, Lp.norm_toLp] using hload (hw j)
    exact hl.trans (mul_le_mul_of_nonneg_left hG hK)
  have hnormal : Tendsto (fun j => ‖G j‖) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let S := max Q ‖F‖
    obtain ⟨κ, hκ, hgap⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (α := Space n) (μ := μ) hf.1 S δ hδ
    have hct : Tendsto (fun j => (p / 2) * |c j| * (K * (Q + ‖F‖))) atTop (𝓝 0) := by
      have h1 := ((hc.abs.const_mul (p / 2)).mul_const (K * (Q + ‖F‖)))
      simpa using h1
    have hsmall : ∀ᶠ j in atTop, (p / 2) * |c j| * (K * (Q + ‖F‖)) < κ :=
      (tendsto_order.mp hct).2 κ hκ
    filter_upwards [hsmall] with j hj
    have hlt : ‖G j‖ < δ := by
      by_contra hnot
      have hdiff : A j - F = G j := by dsimp only [A]; abel
      have hsep : δ ≤ ‖A j - F‖ := by rw [hdiff]; exact le_of_not_gt hnot
      have hg := hgap (A j) F ((hAbound j).trans (le_max_left _ _)) (le_max_right _ _) hsep
      have hm := hmid j
      have he := hupper j
      have hterm : c j * (∫ x in Ω, w j x) ≤ |c j| * (K * (Q + ‖F‖)) := by
        calc c j * (∫ x in Ω, w j x)
            ≤ |c j * (∫ x in Ω, w j x)| := le_abs_self _
          _ = |c j| * |∫ x in Ω, w j x| := abs_mul _ _
          _ ≤ |c j| * (K * (Q + ‖F‖)) := mul_le_mul_of_nonneg_left (hload_bound j) (abs_nonneg _)
      nlinarith [hg, hm, he, hterm, hj, hp0]
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hlt
  have hg : Tendsto (fun j => eLpNorm (gw j) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    have hr : Tendsto (fun j => (eLpNorm (gw j) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0) := by
      simpa only [G, Lp.norm_toLp] using hnormal
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    funext j
    exact (ENNReal.ofReal_toReal (hw j).1.2.2.1.eLpNorm_ne_top).symm
  obtain ⟨P, hP⟩ := exists_W0_Lp_poincare_constant_allp hf.1 hn hΩb
  have hupperlim : Tendsto (fun j => (P : ℝ≥0∞) * eLpNorm (gw j) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr ENNReal.coe_ne_top)
  exact ⟨hg, tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupperlim (fun _ => bot_le) (fun j => hP (hw j))⟩

end ForcedConvergenceAllP

section Optimality
variable {n : ℕ}

/-- First- and second-order optimality conditions at an interior maximizer of
the perturbed doubled objective when `u₁` and `v₁` admit second-order Taylor
expansions at `x₁` and `y₁`. -/
theorem doubled_maximum_optimality {u₁ v₁ : Space n → ℝ}
    {j q η : ℝ} (hq : 1 < q) {x₀ y₀ p₁ p₂ x₁ y₁ : Space n} {r : ℝ}
    (hx₁ : x₁ ∈ ball x₀ r) (hy₁ : y₁ ∈ ball y₀ r)
    {g_u g_v : Space n} {A_u A_v : Space n →L[ℝ] Space n}
    (htu : HasSecondOrderTaylorAt u₁ g_u A_u x₁)
    (htv : HasSecondOrderTaylorAt v₁ g_v A_v y₁)
    (hmax : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall y₀ r,
      u₁ x - v₁ y - j * criticalPowerPenalty q (x - y) -
        η * (‖x - x₀‖ ^ 2 + ‖y - y₀‖ ^ 2) + inner ℝ p₁ x + inner ℝ p₂ y ≤
      u₁ x₁ - v₁ y₁ - j * criticalPowerPenalty q (x₁ - y₁) -
        η * (‖x₁ - x₀‖ ^ 2 + ‖y₁ - y₀‖ ^ 2) + inner ℝ p₁ x₁ + inner ℝ p₂ y₁) :
    g_u = j • gradient (criticalPowerPenalty q) (x₁ - y₁) + (2 * η) • (x₁ - x₀) - p₁ ∧
    g_v = j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂ ∧
    ∀ w : Space n, inner ℝ (A_u w) w ≤ inner ℝ (A_v w) w + (4 * η) * ‖w‖ ^ 2 := by
  have hy₁_cl : y₁ ∈ closedBall y₀ r := ball_subset_closedBall hy₁
  have hx₁_cl : x₁ ∈ closedBall x₀ r := ball_subset_closedBall hx₁
  -- Helper: HasSecondOrderTaylorAt implies HasGradientAt
  have hgrad_of_taylor {f : Space n → ℝ} {g : Space n} {A : Space n →L[ℝ] Space n} {x : Space n}
      (ht : HasSecondOrderTaylorAt f g A x) : HasGradientAt f g x := by
    rw [hasGradientAt_iff_isLittleO]
    have hsq_o : (fun y : Space n => ‖y - x‖ ^ 2) =o[𝓝 x] (fun y : Space n => y - x) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [Metric.ball_mem_nhds x hc] with y hy
      have hd : ‖y - x‖ < c := by simpa [mem_ball, dist_eq_norm] using hy
      rw [Real.norm_of_nonneg (sq_nonneg _), sq]
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
    have h1 := ht.2.trans hsq_o
    have h2 : (fun y => (1 / 2 : ℝ) * inner ℝ (A (y - x)) (y - x)) =o[𝓝 x] (fun y => y - x) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      let δ : ℝ := c / (‖A‖ + 1)
      filter_upwards [Metric.ball_mem_nhds x (show 0 < δ by positivity)] with y hy
      have hd : ‖y - x‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc (1 / 2 : ℝ) * |inner ℝ (A (y - x)) (y - x)|
          ≤ (1 / 2 : ℝ) * (‖A (y - x)‖ * ‖y - x‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
        _ ≤ (1 / 2 : ℝ) * ((‖A‖ * ‖y - x‖) * ‖y - x‖) := by gcongr; exact A.le_opNorm _
        _ ≤ (1 / 2 : ℝ) * ((‖A‖ * δ) * ‖y - x‖) := by gcongr
        _ ≤ (‖A‖ + 1) * δ * ‖y - x‖ := by
            have h1 : (1 / 2 : ℝ) * (‖A‖ * δ) ≤ (‖A‖ + 1) * δ := by
              nlinarith [norm_nonneg A, show 0 < δ by positivity]
            calc (1 / 2 : ℝ) * ((‖A‖ * δ) * ‖y - x‖)
                = ((1 / 2 : ℝ) * (‖A‖ * δ)) * ‖y - x‖ := by ring
              _ ≤ ((‖A‖ + 1) * δ) * ‖y - x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = c * ‖y - x‖ := by dsimp only [δ]; field_simp [(show (0 : ℝ) < ‖A‖ + 1 by positivity).ne']
    have hsum := h1.add h2
    refine hsum.congr' (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun _ => rfl)
    ring
  have hgrad_pen_eq : gradient (criticalPowerPenalty q) (x₁ - y₁) =
      ‖x₁ - y₁‖ ^ (q - 2) • (x₁ - y₁) :=
    (hasGradientAt_criticalPowerPenalty hq (x₁ - y₁)).gradient
  -- First-order in x:
  have hgu : g_u = j • gradient (criticalPowerPenalty q) (x₁ - y₁) + (2 * η) • (x₁ - x₀) - p₁ := by
    let φ₁ : Space n → ℝ := fun x =>
      u₁ x - j * criticalPowerPenalty q (x - y₁) - η * ‖x - x₀‖ ^ 2 + inner ℝ p₁ x
    have hmax₁ : IsLocalMax φ₁ x₁ := by
      filter_upwards [isOpen_ball.mem_nhds hx₁] with x hx
      have h := hmax x (ball_subset_closedBall hx) y₁ hy₁_cl
      dsimp only [φ₁]; linarith
    have hdiff_pen : HasFDerivAt (fun x => criticalPowerPenalty q (x - y₁))
        (toDual ℝ (Space n) (gradient (criticalPowerPenalty q) (x₁ - y₁))) x₁ := by
      have h1 : HasFDerivAt (criticalPowerPenalty q)
          (toDual ℝ (Space n) (gradient (criticalPowerPenalty q) (x₁ - y₁))) (x₁ - y₁) := by
        rw [hgrad_pen_eq]; exact hasGradientAt_criticalPowerPenalty hq (x₁ - y₁)
      have hsub : HasFDerivAt (fun x : Space n => x - y₁) (ContinuousLinearMap.id ℝ (Space n)) x₁ :=
        (hasFDerivAt_id x₁).sub_const y₁
      have h2 := h1.comp x₁ hsub
      exact h2.congr_fderiv (by ext v; simp)
    have hdiff_sq : HasFDerivAt (fun x : Space n => ‖x - x₀‖ ^ 2)
        (toDual ℝ (Space n) ((2 : ℝ) • (x₁ - x₀))) x₁ := by
      have hsub : HasFDerivAt (fun x : Space n => x - x₀) (ContinuousLinearMap.id ℝ (Space n)) x₁ :=
        (hasFDerivAt_id x₁).sub_const x₀
      have hi := hsub.inner ℝ hsub
      refine (hi.congr_of_eventuallyEq (Eventually.of_forall fun x =>
        (real_inner_self_eq_norm_sq (x - x₀)).symm)).congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.id_apply, fderivInnerCLM_apply, toDual_apply_apply,
        real_inner_smul_left, real_inner_comm v (x₁ - x₀)]
      ring
    have hdiff_lin : HasFDerivAt (fun x : Space n => inner ℝ p₁ x)
        (toDual ℝ (Space n) p₁) x₁ :=
      (toDual ℝ (Space n) p₁).hasFDerivAt (x := x₁)
    have hdiff_φ₁ : HasFDerivAt φ₁
        (toDual ℝ (Space n) (g_u - j • gradient (criticalPowerPenalty q) (x₁ - y₁) -
          (2 * η) • (x₁ - x₀) + p₁)) x₁ := by
      have h1 := ((hgrad_of_taylor htu).hasFDerivAt.sub (hdiff_pen.const_mul j)).sub (hdiff_sq.const_mul η)
      have h2 := h1.add hdiff_lin
      refine h2.congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, toDual_apply_apply, smul_eq_mul,
        inner_add_left, inner_sub_left, real_inner_smul_left]
      ring
    have hzero : g_u - j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (x₁ - x₀) + p₁ = 0 := by
      have hf := hmax₁.fderiv_eq_zero
      rw [hdiff_φ₁.fderiv] at hf
      exact (toDual ℝ (Space n)).injective (by simpa using hf)
    calc g_u = (g_u - j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (x₁ - x₀) + p₁) +
          (j • gradient (criticalPowerPenalty q) (x₁ - y₁) + (2 * η) • (x₁ - x₀) - p₁) := by abel
      _ = _ := by rw [hzero, zero_add]
  -- First-order in y:
  have hgv : g_v = j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂ := by
    let φ₂ : Space n → ℝ := fun y =>
      -v₁ y - j * criticalPowerPenalty q (x₁ - y) - η * ‖y - y₀‖ ^ 2 + inner ℝ p₂ y
    have hmax₂ : IsLocalMax φ₂ y₁ := by
      filter_upwards [isOpen_ball.mem_nhds hy₁] with y hy
      have h := hmax x₁ hx₁_cl y (ball_subset_closedBall hy)
      dsimp only [φ₂]; linarith
    have hdiff_pen : HasFDerivAt (fun y => criticalPowerPenalty q (x₁ - y))
        (toDual ℝ (Space n) (-gradient (criticalPowerPenalty q) (x₁ - y₁))) y₁ := by
      have h1 : HasFDerivAt (criticalPowerPenalty q)
          (toDual ℝ (Space n) (gradient (criticalPowerPenalty q) (x₁ - y₁))) (x₁ - y₁) := by
        rw [hgrad_pen_eq]; exact hasGradientAt_criticalPowerPenalty hq (x₁ - y₁)
      have hsub : HasFDerivAt (fun y : Space n => x₁ - y) (-ContinuousLinearMap.id ℝ (Space n)) y₁ :=
        (hasFDerivAt_const x₁ y₁).sub (hasFDerivAt_id y₁) |>.congr_fderiv (by ext v; simp)
      have h2 := h1.comp y₁ hsub
      refine h2.congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, toDual_apply_apply, inner_neg_left, inner_neg_right]
    have hdiff_sq : HasFDerivAt (fun y : Space n => ‖y - y₀‖ ^ 2)
        (toDual ℝ (Space n) ((2 : ℝ) • (y₁ - y₀))) y₁ := by
      have hsub : HasFDerivAt (fun y : Space n => y - y₀) (ContinuousLinearMap.id ℝ (Space n)) y₁ :=
        (hasFDerivAt_id y₁).sub_const y₀
      have hi := hsub.inner ℝ hsub
      refine (hi.congr_of_eventuallyEq (Eventually.of_forall fun y =>
        (real_inner_self_eq_norm_sq (y - y₀)).symm)).congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.id_apply, fderivInnerCLM_apply, toDual_apply_apply,
        real_inner_smul_left, real_inner_comm v (y₁ - y₀)]
      ring
    have hdiff_lin : HasFDerivAt (fun y : Space n => inner ℝ p₂ y)
        (toDual ℝ (Space n) p₂) y₁ :=
      (toDual ℝ (Space n) p₂).hasFDerivAt (x := y₁)
    have hdiff_φ₂ : HasFDerivAt φ₂
        (toDual ℝ (Space n) (-g_v + j • gradient (criticalPowerPenalty q) (x₁ - y₁) -
          (2 * η) • (y₁ - y₀) + p₂)) y₁ := by
      have h1 := ((hgrad_of_taylor htv).hasFDerivAt.neg.sub (hdiff_pen.const_mul j)).sub (hdiff_sq.const_mul η)
      have h2 := h1.add hdiff_lin
      refine h2.congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, toDual_apply_apply,
        smul_eq_mul, inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left]
      ring
    have hzero : -g_v + j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂ = 0 := by
      have hf := hmax₂.fderiv_eq_zero
      rw [hdiff_φ₂.fderiv] at hf
      exact (toDual ℝ (Space n)).injective (by simpa using hf)
    calc g_v = -(-g_v + j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂) +
          (j • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂) := by abel
      _ = _ := by rw [hzero, neg_zero, zero_add]
  -- Second-order along the diagonal (x₁ + t • w, y₁ + t • w):
  refine ⟨hgu, hgv, fun w => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0; simp
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  by_contra hbad
  push Not at hbad
  let γ : ℝ := (inner ℝ (A_u w) w - inner ℝ (A_v w) w - (4 * η) * ‖w‖ ^ 2) / (8 * ‖w‖ ^ 2)
  have hγ : 0 < γ := div_pos (by linarith) (by positivity)
  have hlu := htu.2; rw [Asymptotics.isLittleO_iff] at hlu
  have hlv := htv.2; rw [Asymptotics.isLittleO_iff] at hlv
  obtain ⟨r₁, hr₁, hbu⟩ := Metric.eventually_nhds_iff.mp (hlu hγ)
  obtain ⟨r₂, hr₂, hbv⟩ := Metric.eventually_nhds_iff.mp (hlv hγ)
  obtain ⟨r₃, hr₃, hbx⟩ := Metric.isOpen_iff.mp isOpen_ball x₁ hx₁
  obtain ⟨r₄, hr₄, hby⟩ := Metric.isOpen_iff.mp isOpen_ball y₁ hy₁
  let rmin : ℝ := min (min r₁ r₂) (min r₃ r₄)
  have hrmin : 0 < rmin := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄)
  let t : ℝ := rmin / (2 * ‖w‖)
  have ht : 0 < t := by positivity
  have htw : t * ‖w‖ < rmin := by
    dsimp only [t]; field_simp [hw_pos.ne']; linarith
  have hdist_x : dist (x₁ + t • w) x₁ < r₁ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact htw.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hdist_y : dist (y₁ + t • w) y₁ < r₂ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact htw.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hx_mem : x₁ + t • w ∈ closedBall x₀ r := ball_subset_closedBall (hbx (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact htw.trans_le ((min_le_right _ _).trans (min_le_left _ _))))
  have hy_mem : y₁ + t • w ∈ closedBall y₀ r := ball_subset_closedBall (hby (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    exact htw.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
  have hm := hmax (x₁ + t • w) hx_mem (y₁ + t • w) hy_mem
  have hcancel : (x₁ + t • w) - (y₁ + t • w) = x₁ - y₁ := by abel
  rw [hcancel] at hm
  have hsq_x : ‖(x₁ + t • w) - x₀‖ ^ 2 = ‖x₁ - x₀‖ ^ 2 + 2 * t * inner ℝ (x₁ - x₀) w + t ^ 2 * ‖w‖ ^ 2 := by
    rw [show (x₁ + t • w) - x₀ = (x₁ - x₀) + t • w by abel, norm_add_sq_real,
      real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le]; ring
  have hsq_y : ‖(y₁ + t • w) - y₀‖ ^ 2 = ‖y₁ - y₀‖ ^ 2 + 2 * t * inner ℝ (y₁ - y₀) w + t ^ 2 * ‖w‖ ^ 2 := by
    rw [show (y₁ + t • w) - y₀ = (y₁ - y₀) + t • w by abel, norm_add_sq_real,
      real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le]; ring
  rw [hsq_x, hsq_y, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right] at hm
  -- Notice linear terms cancel identically because g_u - g_v = 2η(x₁-x₀) + 2η(y₁-y₀) - (p₁ + p₂)!
  have hlin_cancel : inner ℝ g_u w - inner ℝ g_v w -
      2 * η * inner ℝ (x₁ - x₀) w - 2 * η * inner ℝ (y₁ - y₀) w +
      inner ℝ p₁ w + inner ℝ p₂ w = 0 := by
    rw [hgu, hgv]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    ring
  have hbu' := (abs_le.mp (by
    simpa [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
      map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_of_nonneg ht.le] using hbu hdist_x)).1
  have hbv' := (abs_le.mp (by
    simpa [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
      map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_of_nonneg ht.le] using hbv hdist_y)).2
  have hγ_eq : 2 * γ * (t * ‖w‖) ^ 2 =
      (1 / 4 : ℝ) * t ^ 2 * (inner ℝ (A_u w) w - inner ℝ (A_v w) w - (4 * η) * ‖w‖ ^ 2) := by
    dsimp only [γ]; field_simp [hw_pos.ne']; ring
  have hfinal : (1 / 4 : ℝ) * t ^ 2 * (inner ℝ (A_u w) w - inner ℝ (A_v w) w - (4 * η) * ‖w‖ ^ 2) ≤ 0 := by
    nlinarith [hm, hbu', hbv', hlin_cancel, hγ_eq]
  have hpos_final : 0 < (1 / 4 : ℝ) * t ^ 2 * (inner ℝ (A_u w) w - inner ℝ (A_v w) w - (4 * η) * ‖w‖ ^ 2) :=
    mul_pos (by positivity) (by linarith)
  linarith

end Optimality

section JLMMain
variable {n : ℕ}

/-- Linear equivalence between `Space n × Space n` and `WithLp 2 (Space n × Space n)`. -/
def prodLpEquiv (n : ℕ) : (Space n × Space n) ≃L[ℝ] WithLp 2 (Space n × Space n) :=
  (WithLp.linearEquiv 2 ℝ (Space n × Space n)).symm.toContinuousLinearEquiv

/-- **Positive-source JLM viscosity comparison** for ALL `1 < p < ∞` and `2 ≤ n`,
requiring only continuity of `u` and `v` (no `C¹` or `C²` regularity). -/
theorem WeakPSourceSupersolutionPair.viscosity_le_allp
    {p c : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ} {g : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v g) (hc : 0 < c)
    (hvc : ContinuousOn v Ω)
    (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u) (huc : ContinuousOn u Ω)
    (hn : 2 ≤ n) (hD : LocalDomain D Ω)
    (hb : ∀ z ∈ frontier D, u z ≤ v z) :
    ∀ z ∈ D, u z ≤ v z := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : Nontrivial (Space n) := by
    refine ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ 1, ?_⟩⟩
    intro h0
    have := congrArg (fun x : Space n => x.ofLp ⟨0, by omega⟩) h0
    simp at this
  intro a ha
  by_contra hbad
  push Not at hbad
  let gap : ℝ := u a - v a
  have hgap : 0 < gap := sub_pos.mpr hbad
  -- Step 1: Compact thickening K ⊆ Ω containing closure D in its interior
  have hcompD : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ₀, hδ₀, hδ₀Ω⟩ := hcompD.exists_cthickening_subset_open hv.2.1 hD.2.2
  let U : Set (Space n) := thickening (δ₀ / 2) (closure D)
  let K : Set (Space n) := closure U
  have hK_sub_cthick : K ⊆ cthickening (δ₀ / 2) (closure D) :=
    closure_thickening_subset_cthickening (δ₀ / 2) (closure D)
  have hKΩ : K ⊆ Ω :=
    hK_sub_cthick.trans ((cthickening_mono (by linarith) (closure D)).trans hδ₀Ω)
  have hKcomp : IsCompact K := (hcompD.isBounded.thickening).isCompact_closure
  have hD_sub_U : closure D ⊆ U := self_subset_thickening (half_pos hδ₀) (closure D)
  have hU_sub_intK : U ⊆ interior K := interior_maximal subset_closure isOpen_thickening
  have hKne : K.Nonempty := ⟨a, subset_closure (hD_sub_U (subset_closure ha))⟩
  have hucK : ContinuousOn u K := huc.mono hKΩ
  have hvcK : ContinuousOn v K := hvc.mono hKΩ
  -- Bounds on |u|, |v|, and radius R of K
  obtain ⟨Mu, hMu_pos, hMu⟩ : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, |u z| ≤ M := by
    obtain ⟨z₀, -, hz⟩ := hKcomp.exists_isMaxOn hKne hucK.abs
    exact ⟨|u z₀| + 1, by positivity, fun z hzK => by have : |u z| ≤ |u z₀| := hz hzK; linarith⟩
  obtain ⟨Mv, hMv_pos, hMv⟩ : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, |v z| ≤ M := by
    obtain ⟨z₀, -, hz⟩ := hKcomp.exists_isMaxOn hKne hvcK.abs
    exact ⟨|v z₀| + 1, by positivity, fun z hzK => by have : |v z| ≤ |v z₀| := hz hzK; linarith⟩
  obtain ⟨R, hR, hKR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
    obtain ⟨R₀, hR₀⟩ := hKcomp.isBounded.subset_closedBall (0 : Space n)
    refine ⟨max R₀ 0, le_max_right _ _, fun z hz => ?_⟩
    have h1 : ‖z‖ ≤ R₀ := by simpa [mem_closedBall, dist_eq_norm] using hR₀ hz
    exact h1.trans (le_max_left _ _)
  -- Step 2: Choose ε > 0 for sup-convolution u₁ and inf-convolution v₁
  obtain ⟨ε₁, hε₁, hu_close⟩ := supConv_uniform_close hKcomp hKne hucK (show 0 < gap / 8 by positivity)
  obtain ⟨ε₂, hε₂, hv_close⟩ := infConv_uniform_close hKcomp hKne hvcK (show 0 < gap / 8 by positivity)
  let ε : ℝ := min (min (ε₁ / 2) (ε₂ / 2))
    (min ((δ₀ / 4) ^ 2 / (8 * Mu)) ((δ₀ / 4) ^ 2 / (8 * Mv)))
  have hε : 0 < ε := lt_min (lt_min (half_pos hε₁) (half_pos hε₂)) (lt_min (by positivity) (by positivity))
  have hε_lt1 : ε < ε₁ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hε₁)
  have hε_lt2 : ε < ε₂ := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hε₂)
  have hmax_in_u : ∀ x ∈ D, ∀ y ∈ K,
      supConv K ε u x = u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2 → y ∈ interior K ∧ y ∈ Ω := by
    intro x hxD y hyK hmax
    have hxK : x ∈ K := subset_closure (hD_sub_U (subset_closure hxD))
    have hsq := supConv_maximizer_dist_sq_le hKcomp hε hucK hMu hxK hyK hmax
    have hlt_sq : ‖x - y‖ ^ 2 < (δ₀ / 4) ^ 2 := by
      have hle : ε ≤ (δ₀ / 4) ^ 2 / (8 * Mu) := (min_le_right _ _).trans (min_le_left _ _)
      have h4Mu : 0 < 4 * Mu := by positivity
      calc ‖x - y‖ ^ 2 ≤ 4 * Mu * ε := hsq
        _ ≤ 4 * Mu * ((δ₀ / 4) ^ 2 / (8 * Mu)) := mul_le_mul_of_nonneg_left hle h4Mu.le
        _ = (δ₀ / 4) ^ 2 / 2 := by field_simp [hMu_pos.ne']; ring
        _ < (δ₀ / 4) ^ 2 := half_lt_self (by positivity)
    have hdist : dist y x < δ₀ / 2 := by
      rw [dist_comm, dist_eq_norm]
      have h1 : ‖x - y‖ < δ₀ / 4 := by nlinarith [norm_nonneg (x - y), hδ₀]
      linarith
    have hyU : y ∈ U := mem_thickening_iff.mpr ⟨x, subset_closure hxD, hdist⟩
    exact ⟨hU_sub_intK hyU, hKΩ (interior_subset (hU_sub_intK hyU))⟩
  have hmin_in_v : ∀ x ∈ D, ∀ z ∈ K,
      infConv K ε v x = v z + (1 / (2 * ε)) * ‖x - z‖ ^ 2 → z ∈ interior K := by
    intro x hxD z hzK hmin
    have hxK : x ∈ K := subset_closure (hD_sub_U (subset_closure hxD))
    have hmax_neg : supConv K ε (-v) x = (-v) z - (1 / (2 * ε)) * ‖x - z‖ ^ 2 := by
      dsimp only [infConv, Pi.neg_apply] at hmin ⊢; linarith
    have hMv_neg : ∀ w ∈ K, |(-v) w| ≤ Mv := fun w hw => by simpa using hMv w hw
    have hsq := supConv_maximizer_dist_sq_le hKcomp hε hvcK.neg hMv_neg hxK hzK hmax_neg
    have hlt_sq : ‖x - z‖ ^ 2 < (δ₀ / 4) ^ 2 := by
      have hle : ε ≤ (δ₀ / 4) ^ 2 / (8 * Mv) := (min_le_right _ _).trans (min_le_right _ _)
      have h4Mv : 0 < 4 * Mv := by positivity
      calc ‖x - z‖ ^ 2 ≤ 4 * Mv * ε := hsq
        _ ≤ 4 * Mv * ((δ₀ / 4) ^ 2 / (8 * Mv)) := mul_le_mul_of_nonneg_left hle h4Mv.le
        _ = (δ₀ / 4) ^ 2 / 2 := by field_simp [hMv_pos.ne']; ring
        _ < (δ₀ / 4) ^ 2 := half_lt_self (by positivity)
    have hdist : dist z x < δ₀ / 2 := by
      rw [dist_comm, dist_eq_norm]
      have h1 : ‖x - z‖ < δ₀ / 4 := by nlinarith [norm_nonneg (x - z), hδ₀]
      linarith
    exact hU_sub_intK (mem_thickening_iff.mpr ⟨x, subset_closure hxD, hdist⟩)
  let u₁ : Space n → ℝ := supConv K ε u
  let v₁ : Space n → ℝ := fun y => infConv K ε v y + gap / 4
  have hu₁_visc : BMCompactAnalytic.IsViscosityPSubsolution p D u₁ :=
    supConv_isViscosityPSubsolution hu hD.1 hKcomp hKne hucK hε hmax_in_u
  have hv₁_contact : ∀ (W : Set (Space n)), IsOpen W → W ⊆ D → ∀ x ∈ W,
      ∀ (φ : Space n → ℝ), ContDiffOn ℝ 1 φ W →
        ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) W →
        v₁ x = φ x → (∀ y ∈ W, y ≠ x → φ y < v₁ y) →
        c ≤ -coordinateDivergence (fun y => pFlux p (gradient φ y)) x := by
    intro W hWopen hWD x hxW φ hφ hF htouch hstrict
    let φ' : Space n → ℝ := fun y => φ y - gap / 4
    have hgrad_eq : gradient φ' = gradient φ := by
      funext y
      change gradient (fun z => φ z + (-(gap / 4))) y = gradient φ y
      exact BMCompactAnalytic.gradient_add_const φ (-(gap / 4)) y
    have hres := infConv_le_neg_divergence_at_strict_contact hv hvc hn hWopen hKcomp hKne hKΩ hε
      hxW (hmin_in_v x (hWD hxW)) (hφ.sub contDiffOn_const)
      (by rw [hgrad_eq]; exact hF)
      (by dsimp only [φ', v₁] at htouch ⊢; linarith)
      (fun y hyW hyne => by have := hstrict y hyW hyne; dsimp only [φ', v₁] at this ⊢; linarith)
    rw [hgrad_eq] at hres
    exact hres
  have hfu_conv : ConvexOn ℝ univ (fun x => u₁ x + (1 / (2 * ε)) * ‖x‖ ^ 2) :=
    supConv_semiconvex_convexOn hKcomp hKne hucK
  have hfu_lip : LipschitzWith (⟨R / ε, by positivity⟩ : ℝ≥0)
      (fun x => u₁ x + (1 / (2 * ε)) * ‖x‖ ^ 2) :=
    supConv_semiconvex_lipschitzWith hKcomp hKne hε hR hKR hucK
  have hfv_conv : ConvexOn ℝ univ (fun y => -v₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) := by
    have h1 := supConv_semiconvex_convexOn (ε := ε) hKcomp hKne hvcK.neg
    have heq : (fun y => -v₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) =
        fun y => (supConv K ε (-v) y + (1 / (2 * ε)) * ‖y‖ ^ 2) + (-(gap / 4)) := by
      funext y; dsimp only [v₁, infConv]; ring
    rw [heq]
    exact h1.add_const (-(gap / 4))
  have hfv_lip : LipschitzWith (⟨R / ε, by positivity⟩ : ℝ≥0)
      (fun y => -v₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) := by
    have h1 := supConv_semiconvex_lipschitzWith hKcomp hKne hε hR hKR hvcK.neg
    have heq : (fun y => -v₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) =
        fun y => (supConv K ε (-v) y + (1 / (2 * ε)) * ‖y‖ ^ 2) - gap / 4 := by
      funext y; dsimp only [v₁, infConv]; ring
    rw [heq]
    refine LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_
    simpa [Real.dist_eq] using h1.dist_le_mul y₁ y₂
  have hu₁_cont : Continuous u₁ := by
    have h1 : Continuous (fun x : Space n => (u₁ x + (1 / (2 * ε)) * ‖x‖ ^ 2) - (1 / (2 * ε)) * ‖x‖ ^ 2) :=
      hfu_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
    simpa only [add_sub_cancel_right] using h1
  have hv₁_cont : Continuous v₁ := by
    have h1 : Continuous (fun y : Space n => -((-v₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) - (1 / (2 * ε)) * ‖y‖ ^ 2)) :=
      (hfv_lip.continuous.sub (continuous_const.mul (continuous_norm.pow 2))).neg
    simpa only [add_sub_cancel_right, neg_neg] using h1
  -- Step 3: Doubled power maximum (x₀, y₀) ∈ D × D with x₀ ≠ y₀
  obtain ⟨k, hk, hflat⟩ := exists_even_flat_contact_exponent hv.1
  let q : ℝ := ((2 * k : ℕ) : ℝ)
  have hq : 1 < q := by
    have hh : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp only [q]; push_cast; linarith
  have hb₁ : ∀ z ∈ frontier D, u₁ z ≤ v₁ z := by
    intro z hz
    have hzK : z ∈ K := subset_closure (hD_sub_U (frontier_subset_closure hz))
    have h1 := (hu_close ε hε hε_lt1 z hzK).2
    have h2 := (hv_close ε hε hε_lt2 z hzK).1
    have h3 := hb z hz
    dsimp only [u₁, v₁]; linarith
  have hgap₁ : 0 < u₁ a - v₁ a := by
    have haK : a ∈ K := subset_closure (hD_sub_U (subset_closure ha))
    have h1 := (hu_close ε hε hε_lt1 a haK).1
    have h2 := (hv_close ε hε hε_lt2 a haK).2
    dsimp only [u₁, v₁, gap] at h1 h2 ⊢; linarith
  obtain ⟨j, hj, x₀, hx₀, y₀, hy₀, _, hm₀⟩ := exists_interior_doubled_power_maximum hD.1 hD.2.1
    hu₁_cont.continuousOn.upperSemicontinuousOn hv₁_cont.continuousOn hb₁ ha hgap₁ hq
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hx₀y₀_ne : x₀ ≠ y₀ := by
    intro heq
    subst heq
    let φ : Space n → ℝ := flatContactPower q ((j : ℝ) + 1) (v₁ x₀) x₀
    have hφ1 : ContDiffOn ℝ 1 φ D := (contDiff_one_flatContactPower hq ((j : ℝ) + 1) (v₁ x₀) x₀).contDiffOn
    have hF1 : ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) D :=
      (contDiff_one_flux_flatContactPower hv.1 hq hflat ((j : ℝ) + 1) (v₁ x₀) x₀).contDiffOn
    have htouch : v₁ x₀ = φ x₀ := by
      dsimp only [φ, flatContactPower, criticalPowerPenalty]
      rw [sub_self, norm_zero, Real.zero_rpow (zero_lt_one.trans hq).ne']; ring
    have hstrict : ∀ y ∈ D, y ≠ x₀ → φ y < v₁ y := by
      intro y hyD hyne
      have hm := hm₀ x₀ (subset_closure hx₀) y (subset_closure hyD)
      have h0 : criticalPowerPenalty q (x₀ - x₀) = 0 := by
        unfold criticalPowerPenalty
        rw [sub_self, norm_zero, Real.zero_rpow (zero_lt_one.trans hq).ne']; ring
      rw [h0, mul_zero, sub_zero] at hm
      have hcomm : criticalPowerPenalty q (x₀ - y) = criticalPowerPenalty q (y - x₀) := by
        unfold criticalPowerPenalty; rw [norm_sub_rev]
      rw [hcomm] at hm
      have hpos_pen : 0 < criticalPowerPenalty q (y - x₀) := by
        unfold criticalPowerPenalty
        have hq0 : 0 < q := zero_lt_one.trans hq
        have hnorm : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
        exact mul_pos (inv_pos.mpr hq0) (Real.rpow_pos_of_pos hnorm q)
      dsimp only [φ, flatContactPower]
      linarith
    have hres := hv₁_contact D hD.1 Subset.rfl x₀ hx₀ φ hφ1 hF1 htouch hstrict
    have hdiv0 : coordinateDivergence (fun y => pFlux p (gradient φ y)) x₀ = 0 :=
      coordinateDivergence_flux_flatContactPower_pole hv.1 hq (zero_lt_one.trans hflat) ((j : ℝ) + 1) (v₁ x₀) x₀
    rw [hdiv0, neg_zero] at hres
    linarith
  -- Step 4: Set up local Jensen perturbation on P := WithLp 2 (Space n × Space n)
  let P := WithLp 2 (Space n × Space n)
  haveI : Nontrivial P := ⟨⟨0, WithLp.toLp 2 (x₀, y₀), fun h0 => by
    have h1 := congrArg (fun z : P => (WithLp.ofLp z).1) h0
    have h2 := congrArg (fun z : P => (WithLp.ofLp z).2) h0
    simp at h1 h2
    exact hx₀y₀_ne (h1.symm.trans h2)⟩⟩
  let e := prodLpEquiv n
  let μP : Measure P := Measure.map e (volume.prod volume)
  haveI : μP.IsAddHaarMeasure := e.isAddHaarMeasure_map (volume.prod volume)
  let z₀ : P := WithLp.toLp 2 (x₀, y₀)
  let ξ₀ : Space n := (j : ℝ) • gradient (criticalPowerPenalty q) (x₀ - y₀)
  have hξ₀_ne : ξ₀ ≠ 0 :=
    smul_ne_zero hj_pos.ne' (gradient_criticalPowerPenalty_ne_zero hq (sub_ne_zero.mpr hx₀y₀_ne))
  have hξ₀_pos : 0 < ‖ξ₀‖ := norm_pos_iff.mpr hξ₀_ne
  -- Uniform operator norm bound K_op = 1 / ε + 1 (we will pick η ≤ 1 / 4)
  let K_op : ℝ := 1 / ε + 1
  have hK_op : 0 ≤ K_op := by positivity
  obtain ⟨δ_g0, hδ_g0, hcont_g0⟩ := matrixClassicalPLaplacian_uniform_close (p := p) hK_op
    (show 0 < c / 4 by positivity) hξ₀_ne
  let δ_g : ℝ := min δ_g0 (‖ξ₀‖ / 2)
  have hδ_g : 0 < δ_g := lt_min hδ_g0 (half_pos hξ₀_pos)
  have hcont_g : ∀ g₁ ∈ ball ξ₀ δ_g, ∀ g₂ ∈ ball ξ₀ δ_g,
      g₁ ≠ 0 ∧ g₂ ≠ 0 ∧ ∀ A : Space n →L[ℝ] Space n, ‖A‖ ≤ K_op →
        |‖g₁‖ ^ (p - 2) * matrixNormalizedPLaplacian p g₁ A -
          ‖g₂‖ ^ (p - 2) * matrixNormalizedPLaplacian p g₂ A| < c / 4 :=
    fun g₁ hg₁ g₂ hg₂ => hcont_g0 g₁ (ball_subset_ball (min_le_left _ _) hg₁)
      g₂ (ball_subset_ball (min_le_left _ _) hg₂)
  let B_p : ℝ := max ((2 * ‖ξ₀‖) ^ (p - 2)) ((‖ξ₀‖ / 2) ^ (p - 2)) + 1
  have hB_p_pos : 0 < B_p := by
    have h1 : 0 ≤ (2 * ‖ξ₀‖) ^ (p - 2) := Real.rpow_nonneg (by positivity) _
    dsimp only [B_p]; linarith [le_max_left ((2 * ‖ξ₀‖) ^ (p - 2)) ((‖ξ₀‖ / 2) ^ (p - 2))]
  have hB_p : ∀ g ∈ ball ξ₀ δ_g, ‖g‖ ^ (p - 2) ≤ B_p := by
    intro g hg
    have hdist : ‖g - ξ₀‖ < ‖ξ₀‖ / 2 := by
      have := mem_ball.mp hg; rw [dist_eq_norm] at this
      exact this.trans_le (min_le_right _ _)
    have hlo : ‖ξ₀‖ / 2 ≤ ‖g‖ := by
      have := norm_sub_norm_le ξ₀ g; rw [norm_sub_rev] at this; linarith
    have hhi : ‖g‖ ≤ 2 * ‖ξ₀‖ := by
      have := norm_add_le (g - ξ₀) ξ₀; rw [sub_add_cancel] at this; linarith
    have hpow : ‖g‖ ^ (p - 2) ≤ max ((2 * ‖ξ₀‖) ^ (p - 2)) ((‖ξ₀‖ / 2) ^ (p - 2)) := by
      rcases le_or_gt 0 (p - 2) with hp2 | hp2
      · exact (Real.rpow_le_rpow (norm_nonneg _) hhi hp2).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_nonpos (half_pos hξ₀_pos) hlo hp2.le).trans (le_max_right _ _)
    dsimp only [B_p]; linarith
  -- Continuity of (x, y) ↦ j • gradient (criticalPowerPenalty q) (x - y) at (x₀, y₀)
  have hgrad_pen_cont : Continuous (fun z : P =>
      (j : ℝ) • gradient (criticalPowerPenalty q) ((WithLp.ofLp z).1 - (WithLp.ofLp z).2)) := by
    have h1 : Continuous (gradient (criticalPowerPenalty q : Space n → ℝ)) := by
      have heq : gradient (criticalPowerPenalty q : Space n → ℝ) =
          fun w => ‖w‖ ^ (q - 2) • w := by
        funext w; exact (hasGradientAt_criticalPowerPenalty hq w).gradient
      rw [heq]
      have hq2 : (0 : ℝ) < q - 2 := by
        have hh : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        dsimp only [q]; push_cast; linarith
      exact (continuous_norm.rpow_const fun _ => Or.inr hq2.le).smul continuous_id
    have hsub : Continuous (fun z : P => (WithLp.ofLp z).1 - (WithLp.ofLp z).2) :=
      (continuous_fst.comp (prodLpEquiv n).symm.continuous).sub
        (continuous_snd.comp (prodLpEquiv n).symm.continuous)
    exact (h1.comp hsub).const_smul (j : ℝ)
  obtain ⟨r_g, hr_g, hr_g_bound⟩ := Metric.continuousAt_iff.mp
    (hgrad_pen_cont.continuousAt (x := z₀)) (δ_g / 3) (by positivity)
  obtain ⟨r_Dx, hr_Dx, hDx₀⟩ := Metric.isOpen_iff.mp hD.1 x₀ hx₀
  obtain ⟨r_Dy, hr_Dy, hDy₀⟩ := Metric.isOpen_iff.mp hD.1 y₀ hy₀
  let r : ℝ := min (min r_g 1) (min (r_Dx / 2) (r_Dy / 2))
  have hr : 0 < r := lt_min (lt_min hr_g zero_lt_one) (lt_min (half_pos hr_Dx) (half_pos hr_Dy))
  let η : ℝ := min (1 / 4 : ℝ) (min (δ_g / (6 * r + 1)) (c / (16 * B_p * ((n : ℝ) + |p - 2| + 1))))
  have hη : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have h4η_le : 4 * η ≤ 1 := by
    have : η ≤ 1 / 4 := min_le_left _ _; linarith
  -- Smoothness of penalty ψ(x, y) = j * criticalPowerPenalty q (x - y) + η * (‖x - x₀‖² + ‖y - y₀‖²)
  let ψ : P → ℝ := fun z =>
    (j : ℝ) * criticalPowerPenalty q ((WithLp.ofLp z).1 - (WithLp.ofLp z).2) +
      η * (‖(WithLp.ofLp z).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z).2 - y₀‖ ^ 2)
  have hψ_c2 : ContDiff ℝ 2 ψ := by
    have hfst : ContDiff ℝ 2 (fun z : P => (WithLp.ofLp z).1) :=
      ((ContinuousLinearMap.fst ℝ (Space n) (Space n)).comp
        (prodLpEquiv n).symm.toContinuousLinearMap).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
    have hsnd : ContDiff ℝ 2 (fun z : P => (WithLp.ofLp z).2) :=
      ((ContinuousLinearMap.snd ℝ (Space n) (Space n)).comp
        (prodLpEquiv n).symm.toContinuousLinearMap).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
    have hpen_eq : (criticalPowerPenalty q : Space n → ℝ) =
        fun w => q⁻¹ * (‖w‖ ^ 2) ^ k := by
      funext w
      unfold criticalPowerPenalty
      have h1 : ‖w‖ ^ q = (‖w‖ ^ 2) ^ k := by
        dsimp only [q]
        rw [Real.rpow_natCast, pow_mul]
      rw [h1]
    have hpen_c2 : ContDiff ℝ 2 (criticalPowerPenalty q : Space n → ℝ) := by
      rw [hpen_eq]
      exact (contDiff_const.mul ((contDiff_id.norm_sq ℝ).pow k)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h1 : ContDiff ℝ 2 (fun z : P => (j : ℝ) * criticalPowerPenalty q ((WithLp.ofLp z).1 - (WithLp.ofLp z).2)) :=
      (contDiff_const (c := (j : ℝ))).mul (hpen_c2.comp (hfst.sub hsnd))
    have h2 : ContDiff ℝ 2 (fun z : P => η * (‖(WithLp.ofLp z).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z).2 - y₀‖ ^ 2)) :=
      (contDiff_const (c := η)).mul
        (((contDiff_id.norm_sq ℝ).of_le (WithTop.coe_le_coe.mpr le_top) |>.comp (hfst.sub contDiff_const)).add
         ((contDiff_id.norm_sq ℝ).of_le (WithTop.coe_le_coe.mpr le_top) |>.comp (hsnd.sub contDiff_const)))
    exact h1.add h2
  obtain ⟨C_ψ, L_ψ, hC_ψ, hψ_conv, hψ_lip⟩ := c2_neg_semiconvex_on_closedBall hψ_c2 z₀ hr
  let h_obj : P → ℝ := fun z => u₁ (WithLp.ofLp z).1 - v₁ (WithLp.ofLp z).2 - ψ z
  let M_tot : ℝ := 1 / ε + C_ψ
  have hM_tot : 0 < M_tot := by positivity
  have hnorm_sq_P (z : P) : ‖z‖ ^ 2 = ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      show inner ℝ z z = inner ℝ (WithLp.ofLp z).1 (WithLp.ofLp z).1 +
        inner ℝ (WithLp.ofLp z).2 (WithLp.ofLp z).2 from rfl,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hfst_le (z : P) : ‖(WithLp.ofLp z).1‖ ≤ ‖z‖ := by
    have := hnorm_sq_P z
    nlinarith [norm_nonneg z, norm_nonneg (WithLp.ofLp z).1, norm_nonneg (WithLp.ofLp z).2]
  have hsnd_le (z : P) : ‖(WithLp.ofLp z).2‖ ≤ ‖z‖ := by
    have := hnorm_sq_P z
    nlinarith [norm_nonneg z, norm_nonneg (WithLp.ofLp z).1, norm_nonneg (WithLp.ofLp z).2]
  have hf_tot_eq : (fun z : P => h_obj z + (M_tot / 2) * ‖z‖ ^ 2) =
      fun z : P =>
        (u₁ (WithLp.ofLp z).1 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).1‖ ^ 2) +
        (-v₁ (WithLp.ofLp z).2 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).2‖ ^ 2) +
        (-ψ z + (C_ψ / 2) * ‖z‖ ^ 2) := by
    funext z
    dsimp only [h_obj, M_tot]
    rw [hnorm_sq_P z]; ring
  have hf_tot_conv : ConvexOn ℝ (closedBall z₀ r) (fun z : P => h_obj z + (M_tot / 2) * ‖z‖ ^ 2) := by
    rw [hf_tot_eq]
    have hc1 : ConvexOn ℝ (closedBall z₀ r)
        (fun z : P => u₁ (WithLp.ofLp z).1 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).1‖ ^ 2) := by
      refine ⟨convex_closedBall z₀ r, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
      exact hfu_conv.2 (mem_univ _) (mem_univ _) ha hb hab
    have hc2 : ConvexOn ℝ (closedBall z₀ r)
        (fun z : P => -v₁ (WithLp.ofLp z).2 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).2‖ ^ 2) := by
      refine ⟨convex_closedBall z₀ r, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
      exact hfv_conv.2 (mem_univ _) (mem_univ _) ha hb hab
    exact (hc1.add hc2).add hψ_conv
  have hf_tot_lip : LipschitzOnWith (⟨R / ε, by positivity⟩ + ⟨R / ε, by positivity⟩ + L_ψ)
      (fun z : P => h_obj z + (M_tot / 2) * ‖z‖ ^ 2) (closedBall z₀ r) := by
    rw [hf_tot_eq]
    have hfst_lip : LipschitzWith 1 (fun z : P => (WithLp.ofLp z).1) :=
      LipschitzWith.of_dist_le_mul fun z₁ z₂ => by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
        exact hfst_le (z₁ - z₂)
    have hsnd_lip : LipschitzWith 1 (fun z : P => (WithLp.ofLp z).2) :=
      LipschitzWith.of_dist_le_mul fun z₁ z₂ => by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
        exact hsnd_le (z₁ - z₂)
    have hl1 : LipschitzOnWith (⟨R / ε, by positivity⟩ : ℝ≥0)
        (fun z : P => u₁ (WithLp.ofLp z).1 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).1‖ ^ 2) (closedBall z₀ r) := by
      rw [← mul_one (⟨R / ε, by positivity⟩ : ℝ≥0)]
      exact (hfu_lip.comp hfst_lip).lipschitzOnWith (s := closedBall z₀ r)
    have hl2 : LipschitzOnWith (⟨R / ε, by positivity⟩ : ℝ≥0)
        (fun z : P => -v₁ (WithLp.ofLp z).2 + (1 / (2 * ε)) * ‖(WithLp.ofLp z).2‖ ^ 2) (closedBall z₀ r) := by
      rw [← mul_one (⟨R / ε, by positivity⟩ : ℝ≥0)]
      exact (hfv_lip.comp hsnd_lip).lipschitzOnWith (s := closedBall z₀ r)
    exact (hl1.add hl2).add hψ_lip
  have hstrict_h : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → h_obj z < h_obj z₀ := by
    intro z hz hzne
    have hdist_z : ‖z - z₀‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hz
    have hx_mem : (WithLp.ofLp z).1 ∈ closure D := by
      apply subset_closure; apply hDx₀
      rw [mem_ball, dist_eq_norm]
      calc ‖(WithLp.ofLp z).1 - x₀‖ ≤ ‖z - z₀‖ := hfst_le (z - z₀)
        _ ≤ r := hdist_z
        _ ≤ r_Dx / 2 := (min_le_right _ _).trans (min_le_left _ _)
        _ < r_Dx := half_lt_self hr_Dx
    have hy_mem : (WithLp.ofLp z).2 ∈ closure D := by
      apply subset_closure; apply hDy₀
      rw [mem_ball, dist_eq_norm]
      calc ‖(WithLp.ofLp z).2 - y₀‖ ≤ ‖z - z₀‖ := hsnd_le (z - z₀)
        _ ≤ r := hdist_z
        _ ≤ r_Dy / 2 := (min_le_right _ _).trans (min_le_right _ _)
        _ < r_Dy := half_lt_self hr_Dy
    have hm := hm₀ (WithLp.ofLp z).1 hx_mem (WithLp.ofLp z).2 hy_mem
    have hpos_sq : 0 < ‖(WithLp.ofLp z).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z).2 - y₀‖ ^ 2 := by
      have hsq : ‖z - z₀‖ ^ 2 = ‖(WithLp.ofLp z).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z).2 - y₀‖ ^ 2 :=
        hnorm_sq_P (z - z₀)
      rw [← hsq]
      exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzne))
    have hz₀_sq : ‖(WithLp.ofLp z₀).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z₀).2 - y₀‖ ^ 2 = 0 := by
      simp [z₀]
    dsimp only [h_obj, ψ]
    rw [hz₀_sq, mul_zero, add_zero]
    have : 0 < η * (‖(WithLp.ofLp z).1 - x₀‖ ^ 2 + ‖(WithLp.ofLp z).2 - y₀‖ ^ 2) :=
      mul_pos hη hpos_sq
    dsimp only [z₀] at *
    linarith
  -- Step 5: Full-measure Alexandrov product set A ⊆ P
  let A₁ : Set (Space n) := {x | DifferentiableAt ℝ (fun y => u₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) x ∧
    ∃ A : Space n →L[ℝ] Space n,
      HasSecondOrderTaylorAt (fun y => u₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2)
        (gradient (fun y => u₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) x) A x}
  let A₂ : Set (Space n) := {y | DifferentiableAt ℝ (fun w => -v₁ w + (1 / (2 * ε)) * ‖w‖ ^ 2) y ∧
    ∃ A : Space n →L[ℝ] Space n,
      HasSecondOrderTaylorAt (fun w => -v₁ w + (1 / (2 * ε)) * ‖w‖ ^ 2)
        (gradient (fun w => -v₁ w + (1 / (2 * ε)) * ‖w‖ ^ 2) y) A y}
  have hA₁_zero : volume A₁ᶜ = 0 := by
    have h := alexandrov_convex_lipschitz (volume : Measure (Space n)) hfu_conv hfu_lip
    rwa [ae_iff] at h
  have hA₂_zero : volume A₂ᶜ = 0 := by
    have h := alexandrov_convex_lipschitz (volume : Measure (Space n)) hfv_conv hfv_lip
    rwa [ae_iff] at h
  let A : Set P := {z | (WithLp.ofLp z).1 ∈ A₁ ∧ (WithLp.ofLp z).2 ∈ A₂}
  have hA_zero : μP Aᶜ = 0 := by
    let N₁ := toMeasurable volume A₁ᶜ
    let N₂ := toMeasurable volume A₂ᶜ
    have hN₁m : MeasurableSet N₁ := measurableSet_toMeasurable volume A₁ᶜ
    have hN₂m : MeasurableSet N₂ := measurableSet_toMeasurable volume A₂ᶜ
    have hN₁z : volume N₁ = 0 := by rw [measure_toMeasurable]; exact hA₁_zero
    have hN₂z : volume N₂ = 0 := by rw [measure_toMeasurable]; exact hA₂_zero
    let B : Set P := e '' ((N₁ ×ˢ univ) ∪ (univ ×ˢ N₂))
    have hsub : Aᶜ ⊆ B := by
      intro z hz
      refine ⟨(WithLp.ofLp z), ?_, rfl⟩
      by_cases h1 : (WithLp.ofLp z).1 ∈ A₁
      · right; exact ⟨mem_univ _, subset_toMeasurable volume A₂ᶜ (fun h2 => hz ⟨h1, h2⟩)⟩
      · left; exact ⟨subset_toMeasurable volume A₁ᶜ h1, mem_univ _⟩
    have hBm : MeasurableSet ((N₁ ×ˢ (univ : Set (Space n))) ∪ ((univ : Set (Space n)) ×ˢ N₂)) :=
      (hN₁m.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hN₂m)
    have hB_eq : e ⁻¹' B = (N₁ ×ˢ (univ : Set (Space n))) ∪ ((univ : Set (Space n)) ×ˢ N₂) :=
      Set.preimage_image_eq _ e.injective
    have hB_meas : MeasurableSet B := by
      have : B = e.symm ⁻¹' ((N₁ ×ˢ (univ : Set (Space n))) ∪ ((univ : Set (Space n)) ×ˢ N₂)) := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩; simpa using hw
        · intro hz; exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
      rw [this]
      exact e.symm.continuous.measurable hBm
    have hBz : μP B = 0 := by
      dsimp only [μP]
      rw [Measure.map_apply e.continuous.measurable hB_meas, hB_eq]
      refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
      rw [Measure.prod_prod, Measure.prod_prod, hN₁z, hN₂z, zero_mul, mul_zero, add_zero]
    exact le_antisymm ((measure_mono hsub).trans hBz.le) bot_le
  -- Step 6: Apply local Jensen's lemma on P!
  obtain ⟨p_vec, hp_ball, z₁, hz₁_ball, hz₁_A, hmax_z₁⟩ :=
    jensen_lemma_exists_good_maximizer μP hM_tot hr hf_tot_conv hf_tot_lip hstrict_h hA_zero
      (show 0 < δ_g / 3 by positivity)
  let x₁ : Space n := (WithLp.ofLp z₁).1
  let y₁ : Space n := (WithLp.ofLp z₁).2
  let p₁ : Space n := (WithLp.ofLp p_vec).1
  let p₂ : Space n := (WithLp.ofLp p_vec).2
  have hz₁_dist : ‖z₁ - z₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hz₁_ball
  have hx₁_ball : x₁ ∈ ball x₀ (r / 2) := by
    rw [mem_ball, dist_eq_norm]
    calc ‖x₁ - x₀‖ ≤ ‖z₁ - z₀‖ := hfst_le (z₁ - z₀)
      _ < r / 3 := hz₁_dist
      _ < r / 2 := by linarith
  have hy₁_ball : y₁ ∈ ball y₀ (r / 2) := by
    rw [mem_ball, dist_eq_norm]
    calc ‖y₁ - y₀‖ ≤ ‖z₁ - z₀‖ := hsnd_le (z₁ - z₀)
      _ < r / 3 := hz₁_dist
      _ < r / 2 := by linarith
  have hx₁_D : x₁ ∈ D := hDx₀ (by
    rw [mem_ball, dist_eq_norm]
    calc ‖x₁ - x₀‖ < r / 2 := by simpa [mem_ball, dist_eq_norm] using hx₁_ball
      _ ≤ r := by linarith
      _ ≤ r_Dx / 2 := (min_le_right _ _).trans (min_le_left _ _)
      _ < r_Dx := half_lt_self hr_Dx)
  have hy₁_D : y₁ ∈ D := hDy₀ (by
    rw [mem_ball, dist_eq_norm]
    calc ‖y₁ - y₀‖ < r / 2 := by simpa [mem_ball, dist_eq_norm] using hy₁_ball
      _ ≤ r := by linarith
      _ ≤ r_Dy / 2 := (min_le_right _ _).trans (min_le_right _ _)
      _ < r_Dy := half_lt_self hr_Dy)
  -- Extract second-order Taylor expansions of u₁ at x₁ and v₁ at y₁
  obtain ⟨hfu_diff, A_fu, htu_f⟩ := hz₁_A.1
  obtain ⟨hfv_diff, A_fv, htv_f⟩ := hz₁_A.2
  let g_u : Space n := gradient (fun y => u₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) x₁ - (1 / ε) • x₁
  let A_u : Space n →L[ℝ] Space n := A_fu - (1 / ε) • ContinuousLinearMap.id ℝ (Space n)
  have htu : HasSecondOrderTaylorAt u₁ g_u A_u x₁ := by
    have h := htu_f.sub_quad (1 / ε)
    have heq : (fun y => (u₁ y + (1 / (2 * ε)) * ‖y‖ ^ 2) - ((1 / ε) / 2) * ‖y‖ ^ 2) = u₁ := by
      funext y; ring
    rwa [heq] at h
  let g_v : Space n := -(gradient (fun w => -v₁ w + (1 / (2 * ε)) * ‖w‖ ^ 2) y₁ - (1 / ε) • y₁)
  let A_v : Space n →L[ℝ] Space n := -(A_fv - (1 / ε) • ContinuousLinearMap.id ℝ (Space n))
  have htv : HasSecondOrderTaylorAt v₁ g_v A_v y₁ := by
    have h1 := (htv_f.sub_quad (1 / ε)).neg
    have heq : (fun w => -((-v₁ w + (1 / (2 * ε)) * ‖w‖ ^ 2) - ((1 / ε) / 2) * ‖w‖ ^ 2)) = v₁ := by
      funext w; ring
    rwa [heq] at h1
  -- Apply doubled_maximum_optimality on closedBall x₀ (r / 2) × closedBall y₀ (r / 2)
  have hmax_half : ∀ x ∈ closedBall x₀ (r / 2), ∀ y ∈ closedBall y₀ (r / 2),
      u₁ x - v₁ y - (j : ℝ) * criticalPowerPenalty q (x - y) -
        η * (‖x - x₀‖ ^ 2 + ‖y - y₀‖ ^ 2) + inner ℝ p₁ x + inner ℝ p₂ y ≤
      u₁ x₁ - v₁ y₁ - (j : ℝ) * criticalPowerPenalty q (x₁ - y₁) -
        η * (‖x₁ - x₀‖ ^ 2 + ‖y₁ - y₀‖ ^ 2) + inner ℝ p₁ x₁ + inner ℝ p₂ y₁ := by
    intro x hx y hy
    let z : P := WithLp.toLp 2 (x, y)
    have hz_cl : z ∈ closedBall z₀ r := by
      rw [mem_closedBall, show dist z z₀ = ‖z - z₀‖ from dist_eq_norm z z₀]
      have hx' : ‖x - x₀‖ ≤ r / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hx
      have hy' : ‖y - y₀‖ ≤ r / 2 := by rw [← dist_eq_norm]; exact mem_closedBall.mp hy
      have hsq : ‖z - z₀‖ ^ 2 ≤ r ^ 2 := by
        rw [hnorm_sq_P (z - z₀)]
        change ‖x - x₀‖ ^ 2 + ‖y - y₀‖ ^ 2 ≤ r ^ 2
        nlinarith [norm_nonneg (x - x₀), norm_nonneg (y - y₀)]
      nlinarith [norm_nonneg (z - z₀), hr]
    have h := hmax_z₁ z hz_cl
    have hinner_z : inner ℝ p_vec z = inner ℝ p₁ x + inner ℝ p₂ y := rfl
    have hinner_z₁ : inner ℝ p_vec z₁ = inner ℝ p₁ x₁ + inner ℝ p₂ y₁ := rfl
    rw [hinner_z, hinner_z₁] at h
    dsimp only [h_obj, ψ, z, x₁, y₁] at h
    linarith
  obtain ⟨hgu_eq, hgv_eq, hhess_le⟩ :=
    doubled_maximum_optimality hq hx₁_ball hy₁_ball htu htv hmax_half
  -- Step 7: Operator norm bound ‖A_v‖ ≤ K_op from semiconvexity/semiconcavity + hhess_le
  have hAu_lo (w : Space n) : -(1 / ε) * ‖w‖ ^ 2 ≤ inner ℝ (A_u w) w := by
    have hsub := IsSubgradient.of_hasFDerivAt hfu_conv hfu_diff.hasFDerivAt
    have hpsd := htu_f.psd_of_convexOn hfu_conv hsub w
    dsimp only [A_u]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith
  have hAv_hi (w : Space n) : inner ℝ (A_v w) w ≤ (1 / ε) * ‖w‖ ^ 2 := by
    have hsub := IsSubgradient.of_hasFDerivAt hfv_conv hfv_diff.hasFDerivAt
    have hpsd := htv_f.psd_of_convexOn hfv_conv hsub w
    dsimp only [A_v]
    simp only [neg_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_neg_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith
  have hAv_norm : ‖A_v‖ ≤ K_op := by
    apply opNorm_le_of_symmetric_quad_bound htv.1 hK_op
    intro w
    rw [abs_le]
    have h1 := hAu_lo w
    have h2 := hhess_le w
    have h3 := hAv_hi w
    dsimp only [K_op]
    constructor <;> nlinarith [sq_nonneg ‖w‖, h4η_le]
  -- Step 8: Show g_u, g_v ∈ ball ξ₀ δ_g and derive contradiction!
  have hξ₁_close : ‖(j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀‖ < δ_g / 3 := by
    have hdist : dist z₁ z₀ < r_g := by
      rw [dist_eq_norm]
      calc ‖z₁ - z₀‖ < r / 3 := hz₁_dist
        _ ≤ r := by linarith
        _ ≤ r_g := (min_le_left _ _).trans (min_le_left _ _)
    have h := hr_g_bound hdist
    rw [dist_eq_norm] at h
    exact h
  have hp₁_small : ‖p₁‖ < δ_g / 3 := by
    have h1 : ‖p_vec‖ < δ_g / 3 := by simpa [mem_ball, dist_eq_norm] using hp_ball
    exact (hfst_le p_vec).trans_lt h1
  have hp₂_small : ‖p₂‖ < δ_g / 3 := by
    have h1 : ‖p_vec‖ < δ_g / 3 := by simpa [mem_ball, dist_eq_norm] using hp_ball
    exact (hsnd_le p_vec).trans_lt h1
  have h2ηr : 2 * η * r < δ_g / 3 := by
    have hle : η ≤ δ_g / (6 * r + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have hpos : (0 : ℝ) < 6 * r + 1 := by positivity
    calc 2 * η * r ≤ 2 * (δ_g / (6 * r + 1)) * r := by gcongr
      _ = (δ_g / 3) * (6 * r / (6 * r + 1)) := by ring
      _ < (δ_g / 3) * 1 := mul_lt_mul_of_pos_left ((div_lt_one hpos).mpr (by linarith)) (by positivity)
      _ = δ_g / 3 := mul_one _
  have hgu_ball : g_u ∈ ball ξ₀ δ_g := by
    rw [mem_ball, dist_eq_norm, hgu_eq]
    have hvec : ((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) + (2 * η) • (x₁ - x₀) - p₁) - ξ₀ =
        ((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) + (2 * η) • (x₁ - x₀) - p₁ := by abel
    rw [hvec]
    have hx_le : ‖x₁ - x₀‖ ≤ r := by
      have := mem_ball.mp hx₁_ball; rw [dist_eq_norm] at this; linarith
    have hterm2 : ‖(2 * η) • (x₁ - x₀)‖ ≤ 2 * η * r := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hx_le (by positivity)
    calc ‖((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) + (2 * η) • (x₁ - x₀) - p₁‖
        ≤ ‖((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) + (2 * η) • (x₁ - x₀)‖ + ‖p₁‖ :=
          norm_sub_le _ _
      _ ≤ ‖(j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀‖ + ‖(2 * η) • (x₁ - x₀)‖ + ‖p₁‖ := by
          gcongr; exact norm_add_le _ _
      _ < δ_g / 3 + δ_g / 3 + δ_g / 3 := by linarith
      _ = δ_g := by ring
  have hgv_ball : g_v ∈ ball ξ₀ δ_g := by
    rw [mem_ball, dist_eq_norm, hgv_eq]
    have hvec : ((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - (2 * η) • (y₁ - y₀) + p₂) - ξ₀ =
        ((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) - (2 * η) • (y₁ - y₀) + p₂ := by abel
    rw [hvec]
    have hy_le : ‖y₁ - y₀‖ ≤ r := by
      have := mem_ball.mp hy₁_ball; rw [dist_eq_norm] at this; linarith
    have hterm2 : ‖(2 * η) • (y₁ - y₀)‖ ≤ 2 * η * r := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hy_le (by positivity)
    calc ‖((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) - (2 * η) • (y₁ - y₀) + p₂‖
        ≤ ‖((j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀) - (2 * η) • (y₁ - y₀)‖ + ‖p₂‖ :=
          norm_add_le _ _
      _ ≤ ‖(j : ℝ) • gradient (criticalPowerPenalty q) (x₁ - y₁) - ξ₀‖ + ‖(2 * η) • (y₁ - y₀)‖ + ‖p₂‖ := by
          gcongr; exact norm_sub_le _ _
      _ < δ_g / 3 + δ_g / 3 + δ_g / 3 := by linarith
      _ = δ_g := by ring
  obtain ⟨hgu_ne, hgv_ne, hdiff_g⟩ := hcont_g g_u hgu_ball g_v hgv_ball
  have hdiff_Av := hdiff_g A_v hAv_norm
  have hsub_ineq : 0 ≤ matrixNormalizedPLaplacian p g_u A_u :=
    htu.matrixNormalizedPLaplacian_nonneg hu₁_visc hx₁_D hgu_ne
  have hsup_ineq : ‖g_v‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_v A_v ≤ -c :=
    htv.matrixClassicalPLaplacian_le_neg_source hD.1 hy₁_D hgv_ne
      (fun W hW hWD hyW => hv₁_contact W hW hWD y₁ hyW)
  have hmono : matrixNormalizedPLaplacian p g_u A_u ≤
      matrixNormalizedPLaplacian p g_u (A_v + (4 * η) • ContinuousLinearMap.id ℝ (Space n)) := by
    apply matrixNormalizedPLaplacian_mono hv.1 hgu_ne
    intro w
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact hhess_le w
  rw [matrixNormalizedPLaplacian_add, matrixNormalizedPLaplacian_smul] at hmono
  have hid_plap : matrixNormalizedPLaplacian p g_u (ContinuousLinearMap.id ℝ (Space n)) =
      (n : ℝ) + (p - 2) := by
    unfold matrixNormalizedPLaplacian
    have htr : LinearMap.trace ℝ (Space n) (ContinuousLinearMap.id ℝ (Space n)).toLinearMap = (n : ℝ) := by
      change LinearMap.trace ℝ (Space n) LinearMap.id = (n : ℝ)
      rw [LinearMap.trace_id, finrank_euclideanSpace_fin]
    have hgu_pos : 0 < ‖g_u‖ := norm_pos_iff.mpr hgu_ne
    rw [htr, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    field_simp [hgu_pos.ne']
  rw [hid_plap] at hmono
  have hgu_rpow_pos : 0 < ‖g_u‖ ^ (p - 2) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hgu_ne) _
  have hη_term : ‖g_u‖ ^ (p - 2) * ((4 * η) * ((n : ℝ) + (p - 2))) ≤ c / 4 := by
    have h1 : ‖g_u‖ ^ (p - 2) ≤ B_p := hB_p g_u hgu_ball
    have h2 : (n : ℝ) + (p - 2) ≤ (n : ℝ) + |p - 2| + 1 := by linarith [le_abs_self (p - 2)]
    have h3 : η ≤ c / (16 * B_p * ((n : ℝ) + |p - 2| + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hden : 0 < 16 * B_p * ((n : ℝ) + |p - 2| + 1) := by positivity
    have h4 : 0 ≤ (4 * η) * ((n : ℝ) + |p - 2| + 1) := by positivity
    calc ‖g_u‖ ^ (p - 2) * ((4 * η) * ((n : ℝ) + (p - 2)))
        ≤ ‖g_u‖ ^ (p - 2) * ((4 * η) * ((n : ℝ) + |p - 2| + 1)) := by gcongr
      _ ≤ B_p * ((4 * η) * ((n : ℝ) + |p - 2| + 1)) := mul_le_mul_of_nonneg_right h1 h4
      _ ≤ B_p * ((4 * (c / (16 * B_p * ((n : ℝ) + |p - 2| + 1)))) * ((n : ℝ) + |p - 2| + 1)) := by gcongr
      _ = c / 4 := by field_simp [hB_p_pos.ne', (show (0 : ℝ) < (n : ℝ) + |p - 2| + 1 by positivity).ne']; ring
  have hstep1 : 0 ≤ ‖g_u‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_u A_u :=
    mul_nonneg hgu_rpow_pos.le hsub_ineq
  have hstep2 : ‖g_u‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_u A_u ≤
      ‖g_u‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_u A_v + c / 4 := by
    have hm' := mul_le_mul_of_nonneg_left hmono hgu_rpow_pos.le
    rw [mul_add] at hm'
    linarith
  have hstep3 : ‖g_u‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_u A_v ≤
      ‖g_v‖ ^ (p - 2) * matrixNormalizedPLaplacian p g_v A_v + c / 4 := by
    linarith [(abs_lt.mp hdiff_Av).2]
  linarith

/-- **General JLM viscosity comparison (manuscript Lemma 3.7)** for ALL
`1 < p < ∞` and ALL dimensions `n ≥ 2`: a continuous viscosity `p`-subsolution
cannot exceed a continuous weak `p`-harmonic function on a relatively compact
domain under boundary order. No `C¹` or `C²` regularity is assumed. -/
theorem WeakPHarmonicPair.viscosity_le_allp
    {p : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ} {g : Space n → Space n}
    (hv : WeakPHarmonicPair p Ω v g) (hvc : ContinuousOn v Ω)
    (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u) (huc : ContinuousOn u Ω)
    (hn : 2 ≤ n) (hD : LocalDomain D Ω)
    (hb : ∀ z ∈ frontier D, u z ≤ v z) :
    ∀ z ∈ D, u z ≤ v z := by
  have hcomp : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ, hδ, hδΩ⟩ := hcomp.exists_cthickening_subset_open hv.2.1 hD.2.2
  let U := thickening δ (closure D)
  have hUl : LocalDomain U Ω := ⟨isOpen_thickening, hcomp.isBounded.thickening,
    (closure_thickening_subset_cthickening δ (closure D)).trans hδΩ⟩
  have hDU : LocalDomain D U := ⟨hD.1, hD.2.1, self_subset_thickening hδ (closure D)⟩
  have hsub : U ⊆ Ω := subset_closure.trans hUl.2.2
  have hS := hv.2.2.1 U hUl
  have hV := hv.mono hsub hUl.1
  let c : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hc_pos (j : ℕ) : 0 < c j := inv_pos.mpr (by positivity)
  have hc_lim : Tendsto c atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  choose V G hVc hVb hVH _ using fun j : ℕ =>
    exists_unique_continuous_source_Dirichlet_allp hv.1 hn hUl.1 hUl.2.1 (c j) hS
  have hVzero : ZeroBoundarySobolevPair p U (v - v) (g - g) := by
    apply (zeroBoundarySobolevPair_zero hv.1 U).congr <;>
      exact Eventually.of_forall fun _ => by simp
  have horder (j : ℕ) : ∀ x ∈ U, v x ≤ V j x :=
    hV.source_zero.leOn_of_ordered_source_continuous_W0 (hVH j) hS (hvc.mono hsub) (hVc j)
      hVzero (hVb j) (hc_pos j).le hn hUl.2.1
  have hle (j : ℕ) : ∀ x ∈ D, u x ≤ V j x := by
    apply (hVH j).supersolution.viscosity_le_allp (hc_pos j) (hVc j)
      (hu.mono hUl.1 hsub) (huc.mono hsub) hn hDU
    intro x hx
    exact (hb x hx).trans (horder j x (hDU.2.2 (frontier_subset_closure hx)))
  have hscal (j : ℕ) : v + (V j - v) = V j := by funext x; simp
  have hgrad (j : ℕ) : g + (G j - g) = G j := by funext x; simp
  have huadd (j : ℕ) : WeakPSourcePair p (c j) U (v + (V j - v)) (g + (G j - g)) := by
    simpa only [hscal, hgrad] using hVH j
  have hlim := (hV.forced_family_W1p_tendsto_allp_gen hS hn hUl.2.1 hVb huadd hc_lim).2
  have hp_ne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hv.1)
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm hp_ne
    (fun j => (hVc j).aestronglyMeasurable hUl.1.measurableSet) hS.2.1.1 hlim
  obtain ⟨σ, _, hσ⟩ := hmeasure.exists_seq_tendsto_ae
  have hDsub : D ⊆ U := subset_closure.trans hDU.2.2
  have hσD := ae_mono (Measure.restrict_mono_set _ hDsub) hσ
  have hae : (fun x => max (u x) (v x)) =ᵐ[volume.restrict D] v := by
    filter_upwards [hσD, ae_restrict_mem hD.1.measurableSet] with x hx hxD
    exact max_eq_right (le_of_tendsto_of_tendsto' tendsto_const_nhds hx (fun j => hle (σ j) x hxD))
  have hvD := hvc.mono (hDsub.trans hsub)
  have huD := huc.mono (hDsub.trans hsub)
  have he := Measure.eqOn_open_of_ae_eq hae hD.1 (huD.sup hvD) hvD
  intro x hx
  exact (le_max_left _ _).trans (he hx).le

end JLMMain
end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.forced_family_W1p_tendsto_allp_gen
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.viscosity_le_allp
#print axioms BMCompactPDE.WeakPHarmonicPair.viscosity_le_allp

