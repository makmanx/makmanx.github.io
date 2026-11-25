import AlexandrovConvex

/-! Local Jensen's lemma for semiconvex functions on a closed ball in a
finite-dimensional real inner product space: any strict maximum on `closedBall x₀ r`
at `x₀` can be perturbed by an arbitrarily small linear functional so that the
perturbed maximizer falls in any full-measure set (e.g. the Alexandrov set). -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal
namespace BMCompactPDE

section LocalJensen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A local subgradient on `closedBall x₀ r` exists at every interior point of
a convex Lipschitz function on `closedBall x₀ r`. -/
theorem exists_local_subgradient
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : ℝ≥0} {x₀ : E} {r : ℝ} (hr : 0 < r) {f : E → ℝ}
    (hf_conv : ConvexOn ℝ (closedBall x₀ r) f)
    (hf_lip : LipschitzOnWith L f (closedBall x₀ r))
    {x : E} (hx : x ∈ ball x₀ r) :
    ∃ q : E, ∀ y ∈ closedBall x₀ r, f x + inner ℝ q (y - x) ≤ f y := by
  have hae : ∀ᵐ y ∂(μ.restrict (closedBall x₀ r)), DifferentiableWithinAt ℝ f (closedBall x₀ r) y :=
    hf_lip.ae_differentiableWithinAt isClosed_closedBall.measurableSet
  have hae_ball : ∀ᵐ y ∂(μ.restrict (ball x₀ r)), DifferentiableAt ℝ f y := by
    have h1 := ae_mono (Measure.restrict_mono ball_subset_closedBall le_rfl) hae
    filter_upwards [h1, ae_restrict_mem isOpen_ball.measurableSet] with y hy hyb
    exact hy.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hyb) ball_subset_closedBall)
  have hex_seq : ∀ k : ℕ, ∃ y ∈ ball x₀ r ∩ ball x ((k : ℝ) + 1)⁻¹, DifferentiableAt ℝ f y := by
    intro k
    let U := ball x₀ r ∩ ball x ((k : ℝ) + 1)⁻¹
    have hUopen : IsOpen U := isOpen_ball.inter isOpen_ball
    have hUne : U.Nonempty := ⟨x, hx, mem_ball_self (by positivity)⟩
    have hUpos : μ U ≠ 0 := Measure.IsOpenPosMeasure.open_pos U hUopen hUne
    have hnot : ¬ (U ⊆ {y | ¬ DifferentiableAt ℝ f y}) := by
      intro hsub
      have hzero : μ (ball x₀ r ∩ {y | ¬ DifferentiableAt ℝ f y}) = 0 := by
        rw [ae_restrict_iff' isOpen_ball.measurableSet] at hae_ball
        rw [ae_iff] at hae_ball
        convert hae_ball using 2
        ext y; simp
      have hUle : μ U ≤ μ (ball x₀ r ∩ {y | ¬ DifferentiableAt ℝ f y}) :=
        measure_mono (fun y hy => ⟨hy.1, hsub hy⟩)
      exact hUpos (le_antisymm (hUle.trans hzero.le) bot_le)
    rw [Set.not_subset] at hnot
    obtain ⟨y, hyU, hyd⟩ := hnot
    exact ⟨y, hyU, not_not.mp hyd⟩
  choose u hu_mem hu_diff using hex_seq
  have hu_lim : Tendsto u atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ε⁻¹
    refine ⟨N, fun k hk => ?_⟩
    have h1 : dist (u k) x < ((k : ℝ) + 1)⁻¹ := mem_ball.mp (hu_mem k).2
    have h2 : ((k : ℝ) + 1)⁻¹ < ε := by
      rw [inv_lt_comm₀ (by positivity) hε]
      have hk' : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    exact h1.trans h2
  have hsub_u (k : ℕ) : ∀ y ∈ closedBall x₀ r,
      f (u k) + inner ℝ (gradient f (u k)) (y - u k) ≤ f y := by
    intro y hy
    have hD : HasFDerivAt f (toDual ℝ E (gradient f (u k))) (u k + (0 : ℝ) • (y - u k)) := by
      simpa using (hu_diff k).hasGradientAt.hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => f (u k + t • (y - u k)))
        (inner ℝ (gradient f (u k)) (y - u k)) 0 := by
      have hline : HasDerivAt (fun t : ℝ => u k + t • (y - u k)) (y - u k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - u k)).const_add (u k)
      have h := hD.comp_hasDerivAt 0 hline
      rwa [toDual_apply_apply] at h
    have hlim := hcomp.tendsto_slope_zero_right
    have hle : inner ℝ (gradient f (u k)) (y - u k) ≤ f y - f (u k) := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      have hconv := hf_conv.2 (ball_subset_closedBall (hu_mem k).1) hy
        (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
      have hpt : (1 - t) • u k + t • y = u k + t • (y - u k) := by module
      rw [hpt] at hconv
      simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hconv ⊢
      rw [← div_eq_inv_mul, div_le_iff₀ ht.1]
      linarith
    linarith
  have hnorm_u (k : ℕ) : ‖gradient f (u k)‖ ≤ L := by
    have huk_ball : u k ∈ ball x₀ r := (hu_mem k).1
    obtain ⟨ρ, hρ, hρ_sub⟩ := Metric.isOpen_iff.mp isOpen_ball (u k) huk_ball
    by_cases hg0 : gradient f (u k) = 0
    · rw [hg0, norm_zero]; exact NNReal.coe_nonneg L
    · have hgpos : 0 < ‖gradient f (u k)‖ := norm_pos_iff.mpr hg0
      let t : ℝ := ρ / (2 * ‖gradient f (u k)‖)
      have ht : 0 < t := by positivity
      let y : E := u k + t • gradient f (u k)
      have hy_cl : y ∈ closedBall x₀ r := ball_subset_closedBall (hρ_sub (by
        rw [mem_ball, dist_eq_norm, show y - u k = t • gradient f (u k) by dsimp only [y]; abel,
          norm_smul, Real.norm_of_nonneg ht.le]
        dsimp only [t]; field_simp [hgpos.ne']; linarith))
      have h1 := hsub_u k y hy_cl
      have hdiff : y - u k = t • gradient f (u k) := by dsimp only [y]; abel
      rw [hdiff, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
      have h2 : f y - f (u k) ≤ (L : ℝ) * (t * ‖gradient f (u k)‖) := by
        calc f y - f (u k) ≤ |f y - f (u k)| := le_abs_self _
          _ = dist (f y) (f (u k)) := (Real.dist_eq _ _).symm
          _ ≤ (L : ℝ) * dist y (u k) := hf_lip.dist_le_mul y hy_cl (u k) (ball_subset_closedBall huk_ball)
          _ = (L : ℝ) * (t * ‖gradient f (u k)‖) := by
              rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg ht.le]
      have h3 : t * ‖gradient f (u k)‖ ^ 2 ≤ (L : ℝ) * (t * ‖gradient f (u k)‖) := by linarith
      have hpos_tg : 0 < t * ‖gradient f (u k)‖ := mul_pos ht hgpos
      nlinarith
  have hmem (k : ℕ) : gradient f (u k) ∈ closedBall (0 : E) (L : ℝ) := by
    rw [mem_closedBall_zero_iff]; exact hnorm_u k
  obtain ⟨q, -, φ, hφ, hq_lim⟩ := (isCompact_closedBall (0 : E) (L : ℝ)).tendsto_subseq hmem
  refine ⟨q, fun y hy => ?_⟩
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 x) := hu_lim.comp hφ.tendsto_atTop
  have hf_cont_x : ContinuousAt f x :=
    (hf_lip.continuousOn.continuousAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall))
  have hlhs : Tendsto (fun k => f (u (φ k)) + inner ℝ (gradient f (u (φ k))) (y - u (φ k)))
      atTop (𝓝 (f x + inner ℝ q (y - x))) :=
    (hf_cont_x.tendsto.comp huφ).add (hq_lim.inner (tendsto_const_nhds.sub huφ))
  exact le_of_tendsto hlhs (Eventually.of_forall fun k => hsub_u (φ k) y hy)

/-- **Local Jensen's lemma**: if `h(x) + (M/2)‖x‖²` is convex and Lipschitz on
`closedBall x₀ r`, and `h` attains a strict maximum on `closedBall x₀ r` at `x₀`,
then for any full-measure set `A` and any `δ > 0`, there exists `p ∈ ball 0 δ`
and `x ∈ ball x₀ (r / 3) ∩ A` maximizing `y ↦ h y + ⟪p, y⟫` on `closedBall x₀ r`. -/
theorem jensen_lemma_exists_good_maximizer
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {L : ℝ≥0} {M : ℝ} (hM : 0 < M) {h : E → ℝ}
    {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hf_conv : ConvexOn ℝ (closedBall x₀ r) (fun x => h x + (M / 2) * ‖x‖ ^ 2))
    (hf_lip : LipschitzOnWith L (fun x => h x + (M / 2) * ‖x‖ ^ 2) (closedBall x₀ r))
    (hstrict : ∀ y ∈ closedBall x₀ r, y ≠ x₀ → h y < h x₀)
    {A : Set E} (hA : μ Aᶜ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p ∈ ball (0 : E) δ, ∃ x ∈ ball x₀ (r / 3), x ∈ A ∧
      ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x := by
  classical
  let f : E → ℝ := fun x => h x + (M / 2) * ‖x‖ ^ 2
  have hh_cont : ContinuousOn h (closedBall x₀ r) := by
    have hq : ContinuousOn (fun x : E => (M / 2) * ‖x‖ ^ 2) (closedBall x₀ r) :=
      (continuous_const.mul (continuous_norm.pow 2)).continuousOn
    have h1 : ContinuousOn (fun x : E => (h x + (M / 2) * ‖x‖ ^ 2) - (M / 2) * ‖x‖ ^ 2)
        (closedBall x₀ r) := hf_lip.continuousOn.sub hq
    simpa only [add_sub_cancel_right] using h1
  let S : Set E := closedBall x₀ r \ ball x₀ (r / 3)
  have hS_comp : IsCompact S := (isCompact_closedBall x₀ r).diff isOpen_ball
  have hgap : ∃ γ : ℝ, 0 < γ ∧ ∀ y ∈ S, h y ≤ h x₀ - γ := by
    by_cases hSne : S.Nonempty
    · obtain ⟨y, hyS, hymax⟩ := hS_comp.exists_isMaxOn hSne (hh_cont.mono diff_subset)
      have hy_ne : y ≠ x₀ := by
        intro heq; subst heq
        exact hyS.2 (mem_ball_self (by positivity))
      have hlt : h y < h x₀ := hstrict y hyS.1 hy_ne
      refine ⟨h x₀ - h y, sub_pos.mpr hlt, fun z hz => ?_⟩
      have hle : h z ≤ h y := hymax hz
      linarith
    · refine ⟨1, zero_lt_one, fun z hz => (hSne ⟨z, hz⟩).elim⟩
  obtain ⟨γ, hγ, hS_bound⟩ := hgap
  let δ' : ℝ := min δ (γ / (2 * r + 1))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hδ'_le : δ' ≤ δ := min_le_left _ _
  let K : Set E := {x ∈ ball x₀ (r / 3) | ∃ p ∈ ball (0 : E) δ',
    ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x}
  have hex_max (p : E) (hp : p ∈ ball (0 : E) δ') :
      ∃ x ∈ K, ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x := by
    have hcont_p : ContinuousOn (fun y => h y + inner ℝ p y) (closedBall x₀ r) :=
      hh_cont.add (continuous_const.inner continuous_id).continuousOn
    obtain ⟨x, hx_cl, hx_max⟩ :=
      (isCompact_closedBall x₀ r).exists_isMaxOn (nonempty_closedBall.mpr hr.le) hcont_p
    have hx_ball : x ∈ ball x₀ (r / 3) := by
      by_contra hx_not
      have hxS : x ∈ S := ⟨hx_cl, hx_not⟩
      have h1 := hS_bound x hxS
      have h2 : h x₀ + inner ℝ p x₀ ≤ h x + inner ℝ p x := hx_max (mem_closedBall_self hr.le)
      have h3 : γ ≤ inner ℝ p (x - x₀) := by rw [inner_sub_right]; linarith
      have h4 : ‖p‖ < δ' := by simpa [mem_ball, dist_eq_norm] using hp
      have h5 : ‖x - x₀‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hx_cl
      have h6 : δ' * r < γ := by
        have hle : δ' ≤ γ / (2 * r + 1) := min_le_right _ _
        have hpos : (0 : ℝ) < 2 * r + 1 := by positivity
        calc δ' * r ≤ (γ / (2 * r + 1)) * r := mul_le_mul_of_nonneg_right hle hr.le
          _ = γ * (r / (2 * r + 1)) := by ring
          _ < γ * 1 := mul_lt_mul_of_pos_left ((div_lt_one hpos).mpr (by linarith)) hγ
          _ = γ := mul_one γ
      have h7 : inner ℝ p (x - x₀) ≤ ‖p‖ * ‖x - x₀‖ := real_inner_le_norm _ _
      have h8 : ‖p‖ * ‖x - x₀‖ ≤ δ' * r :=
        mul_le_mul h4.le h5 (norm_nonneg _) hδ'.le
      linarith
    exact ⟨x, ⟨hx_ball, p, hp, hx_max⟩, hx_max⟩
  have hupper_f {x p : E} (hmax : ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x)
      {y : E} (hy : y ∈ closedBall x₀ r) :
      f y - f x ≤ inner ℝ (M • x - p) (y - x) + (M / 2) * ‖y - x‖ ^ 2 := by
    have h1 := hmax y hy
    have hnorm : ‖y‖ ^ 2 - ‖x‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * inner ℝ x (y - x) := by
      have hvec : y = (y - x) + x := by abel
      conv_lhs => rw [hvec, norm_add_sq_real]
      rw [real_inner_comm (y - x) x]; ring
    rw [inner_sub_left, real_inner_smul_left]
    have h2 : f y - f x = (h y - h x) + (M / 2) * (‖y‖ ^ 2 - ‖x‖ ^ 2) := by
      dsimp only [f]; ring
    rw [h2, hnorm]
    have h3 : inner ℝ p (y - x) = inner ℝ p y - inner ℝ p x := inner_sub_right _ _ _
    linarith
  have hsub_of_max {x p : E} (hx : x ∈ ball x₀ (r / 3))
      (hmax : ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x) :
      ∀ y ∈ closedBall x₀ r, f x + inner ℝ (M • x - p) (y - x) ≤ f y := by
    have hx_r : x ∈ ball x₀ r := ball_subset_ball (by linarith) hx
    obtain ⟨q, hq⟩ := exists_local_subgradient μ hr hf_conv hf_lip hx_r
    have hle : ∀ v : E, inner ℝ q v ≤ inner ℝ (M • x - p) v := by
      intro v
      have hx_lt : ‖x - x₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hx
      have hlim : Tendsto (fun t : ℝ => (M / 2) * t * ‖v‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun t : ℝ => (M / 2) * t * ‖v‖ ^ 2) (𝓝 0)
            (𝓝 ((M / 2) * 0 * ‖v‖ ^ 2)) :=
          ((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto
        simpa using h1.mono_left nhdsWithin_le_nhds
      have hlim' : Tendsto (fun t : ℝ =>
          inner ℝ (M • x - p) v - inner ℝ q v + (M / 2) * t * ‖v‖ ^ 2)
          (𝓝[>] 0) (𝓝 (inner ℝ (M • x - p) v - inner ℝ q v)) := by
        simpa using hlim.const_add (inner ℝ (M • x - p) v - inner ℝ q v)
      have hge : 0 ≤ inner ℝ (M • x - p) v - inner ℝ q v := by
        apply ge_of_tendsto hlim'
        let t₀ : ℝ := (r / 2) / (‖v‖ + 1)
        have ht₀ : 0 < t₀ := by positivity
        filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
        have hyt : x + t • v ∈ closedBall x₀ r := by
          rw [mem_closedBall, dist_eq_norm, show x + t • v - x₀ = (x - x₀) + t • v by abel]
          calc ‖(x - x₀) + t • v‖ ≤ ‖x - x₀‖ + ‖t • v‖ := norm_add_le _ _
            _ = ‖x - x₀‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1.le]
            _ ≤ r / 3 + t₀ * ‖v‖ := by gcongr; exact ht.2.le
            _ ≤ r / 3 + r / 2 := by
                have : t₀ * ‖v‖ ≤ r / 2 := by
                  dsimp only [t₀]
                  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                  nlinarith [norm_nonneg v]
                linarith
            _ ≤ r := by linarith
        have h1 := hq (x + t • v) hyt
        have h2 := hupper_f hmax hyt
        rw [add_sub_cancel_left, real_inner_smul_right] at h1
        rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.1.le] at h2
        have hmul : 0 ≤ t * (inner ℝ (M • x - p) v - inner ℝ q v + (M / 2) * t * ‖v‖ ^ 2) := by
          dsimp only [f] at h2; nlinarith
        exact nonneg_of_mul_nonneg_right hmul ht.1
      linarith
    have heq : q = M • x - p := by
      have h1 := hle (q - (M • x - p))
      have h2 : inner ℝ (q - (M • x - p)) (q - (M • x - p)) ≤ 0 := by
        rw [inner_sub_left]; linarith
      rw [real_inner_self_eq_norm_sq] at h2
      exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (q - (M • x - p))]))
    exact heq ▸ hq
  let P : E → E := fun x => if hx : x ∈ K then hx.2.choose else 0
  have hP_spec (x : E) (hx : x ∈ K) :
      P x ∈ ball (0 : E) δ' ∧ ∀ y ∈ closedBall x₀ r, h y + inner ℝ (P x) y ≤ h x + inner ℝ (P x) x := by
    simp only [P, dif_pos hx]
    exact hx.2.choose_spec
  have hP_eq_of_max {x p : E} (hx : x ∈ K)
      (hmax : ∀ y ∈ closedBall x₀ r, h y + inner ℝ p y ≤ h x + inner ℝ p x) : P x = p := by
    have hsub1 := hsub_of_max hx.1 (hP_spec x hx).2
    have hle_both (v : E) : inner ℝ (M • x - P x) v ≤ inner ℝ (M • x - p) v := by
      have hx_lt : ‖x - x₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hx.1
      have hlim : Tendsto (fun t : ℝ => (M / 2) * t * ‖v‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun t : ℝ => (M / 2) * t * ‖v‖ ^ 2) (𝓝 0)
            (𝓝 ((M / 2) * 0 * ‖v‖ ^ 2)) :=
          ((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto
        simpa using h1.mono_left nhdsWithin_le_nhds
      have hlim' : Tendsto (fun t : ℝ =>
          inner ℝ (M • x - p) v - inner ℝ (M • x - P x) v + (M / 2) * t * ‖v‖ ^ 2)
          (𝓝[>] 0) (𝓝 (inner ℝ (M • x - p) v - inner ℝ (M • x - P x) v)) := by
        simpa using hlim.const_add (inner ℝ (M • x - p) v - inner ℝ (M • x - P x) v)
      have hge : 0 ≤ inner ℝ (M • x - p) v - inner ℝ (M • x - P x) v := by
        apply ge_of_tendsto hlim'
        let t₀ : ℝ := (r / 2) / (‖v‖ + 1)
        have ht₀ : 0 < t₀ := by positivity
        filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
        have hyt : x + t • v ∈ closedBall x₀ r := by
          rw [mem_closedBall, dist_eq_norm, show x + t • v - x₀ = (x - x₀) + t • v by abel]
          calc ‖(x - x₀) + t • v‖ ≤ ‖x - x₀‖ + ‖t • v‖ := norm_add_le _ _
            _ = ‖x - x₀‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.1.le]
            _ ≤ r / 3 + t₀ * ‖v‖ := by gcongr; exact ht.2.le
            _ ≤ r / 3 + r / 2 := by
                have : t₀ * ‖v‖ ≤ r / 2 := by
                  dsimp only [t₀]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                  nlinarith [norm_nonneg v]
                linarith
            _ ≤ r := by linarith
        have h1 := hsub1 (x + t • v) hyt
        have h2 := hupper_f hmax hyt
        rw [add_sub_cancel_left, real_inner_smul_right] at h1
        rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.1.le] at h2
        have hmul : 0 ≤ t * (inner ℝ (M • x - p) v - inner ℝ (M • x - P x) v + (M / 2) * t * ‖v‖ ^ 2) := by
          nlinarith
        exact nonneg_of_mul_nonneg_right hmul ht.1
      linarith
    have hdiff : (M • x - P x) - (M • x - p) = p - P x := by abel
    have h1 := hle_both (p - P x)
    have h2 : inner ℝ ((M • x - P x) - (M • x - p)) (p - P x) ≤ 0 := by
      rw [inner_sub_left]; linarith
    rw [hdiff, real_inner_self_eq_norm_sq] at h2
    exact (sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (p - P x)]))).symm
  have hP_lip : LipschitzOnWith (⟨3 * M, by positivity⟩ : ℝ≥0) P K := by
    refine LipschitzOnWith.of_dist_le_mul fun x₁ hx₁ x₂ hx₂ => ?_
    change dist (P x₁) (P x₂) ≤ (3 * M) * dist x₁ x₂
    rw [dist_eq_norm, dist_eq_norm]
    set q₁ := M • x₁ - P x₁
    set q₂ := M • x₂ - P x₂
    have hq₁ := hsub_of_max hx₁.1 (hP_spec x₁ hx₁).2
    have hq₂ := hsub_of_max hx₂.1 (hP_spec x₂ hx₂).2
    have hq_dist : ‖q₂ - q₁‖ ≤ 2 * M * ‖x₂ - x₁‖ := by
      by_cases hu : q₂ - q₁ = 0
      · rw [hu, norm_zero]; positivity
      · have hu_pos : 0 < ‖q₂ - q₁‖ := norm_pos_iff.mpr hu
        let v : E := (‖x₂ - x₁‖ / ‖q₂ - q₁‖) • (q₂ - q₁)
        have hv_norm : ‖v‖ = ‖x₂ - x₁‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hu_pos.ne']
        have hx₁_lt : ‖x₁ - x₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hx₁.1
        have hx₂_lt : ‖x₂ - x₀‖ < r / 3 := by simpa [mem_ball, dist_eq_norm] using hx₂.1
        have hxv_mem : x₂ + v ∈ closedBall x₀ r := by
          rw [mem_closedBall, dist_eq_norm, show x₂ + v - x₀ = (x₂ - x₀) + v by abel]
          have h12 : ‖x₂ - x₁‖ ≤ ‖x₂ - x₀‖ + ‖x₁ - x₀‖ := by
            rw [show x₂ - x₁ = (x₂ - x₀) - (x₁ - x₀) by abel]
            exact norm_sub_le _ _
          calc ‖(x₂ - x₀) + v‖ ≤ ‖x₂ - x₀‖ + ‖v‖ := norm_add_le _ _
            _ = ‖x₂ - x₀‖ + ‖x₂ - x₁‖ := by rw [hv_norm]
            _ ≤ ‖x₂ - x₀‖ + (‖x₂ - x₀‖ + ‖x₁ - x₀‖) := by linarith
            _ ≤ r := by linarith
        have hx₂_cl : x₂ ∈ closedBall x₀ r := ball_subset_closedBall (ball_subset_ball (by linarith) hx₂.1)
        have h1 := hq₁ x₂ hx₂_cl
        have h2 := hq₂ (x₂ + v) hxv_mem
        rw [add_sub_cancel_left] at h2
        have h3 := hupper_f (hP_spec x₁ hx₁).2 hxv_mem
        have hvec1 : x₂ + v - x₁ = (x₂ - x₁) + v := by abel
        rw [hvec1, inner_add_right] at h3
        have hinner : inner ℝ (q₂ - q₁) v ≤ (M / 2) * ‖(x₂ - x₁) + v‖ ^ 2 := by
          rw [inner_sub_left]; linarith
        have hlhs : inner ℝ (q₂ - q₁) v = ‖x₂ - x₁‖ * ‖q₂ - q₁‖ := by
          dsimp only [v]
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp [hu_pos.ne']
        have hrhs : ‖(x₂ - x₁) + v‖ ≤ 2 * ‖x₂ - x₁‖ := by
          calc ‖(x₂ - x₁) + v‖ ≤ ‖x₂ - x₁‖ + ‖v‖ := norm_add_le _ _
            _ = 2 * ‖x₂ - x₁‖ := by rw [hv_norm]; ring
        have hsq : ‖x₂ - x₁‖ * ‖q₂ - q₁‖ ≤ 2 * M * ‖x₂ - x₁‖ ^ 2 := by
          rw [← hlhs]
          calc inner ℝ (q₂ - q₁) v ≤ (M / 2) * ‖(x₂ - x₁) + v‖ ^ 2 := hinner
            _ ≤ (M / 2) * (2 * ‖x₂ - x₁‖) ^ 2 := by gcongr
            _ = 2 * M * ‖x₂ - x₁‖ ^ 2 := by ring
        by_cases hx12 : ‖x₂ - x₁‖ = 0
        · have heq : x₂ = x₁ := sub_eq_zero.mp (norm_eq_zero.mp hx12)
          subst heq; simp [q₁, q₂] at hu
        · have hx12_pos : 0 < ‖x₂ - x₁‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx12)
          nlinarith
    have hP_diff : P x₁ - P x₂ = M • (x₁ - x₂) + (q₂ - q₁) := by
      dsimp only [q₁, q₂]; module
    rw [hP_diff]
    calc ‖M • (x₁ - x₂) + (q₂ - q₁)‖
        ≤ ‖M • (x₁ - x₂)‖ + ‖q₂ - q₁‖ := norm_add_le _ _
      _ = M * ‖x₁ - x₂‖ + ‖q₂ - q₁‖ := by rw [norm_smul, Real.norm_of_nonneg hM.le]
      _ ≤ M * ‖x₁ - x₂‖ + 2 * M * ‖x₂ - x₁‖ := by linarith
      _ = 3 * M * ‖x₁ - x₂‖ := by rw [norm_sub_rev x₂ x₁]; ring
  have hball_sub : ball (0 : E) δ' ⊆ P '' K := by
    intro p hp
    obtain ⟨x, hxK, hmax⟩ := hex_max p hp
    exact ⟨x, hxK, hP_eq_of_max hxK hmax⟩
  have hK_ne_zero : μ K ≠ 0 := by
    intro hKz
    have hP_zero := addHaar_image_eq_zero_of_lipschitzOnWith μ hP_lip hKz
    have hball_zero : μ (ball (0 : E) δ') = 0 :=
      le_antisymm ((measure_mono hball_sub).trans hP_zero.le) bot_le
    exact Measure.IsOpenPosMeasure.open_pos (ball (0 : E) δ') isOpen_ball
      (nonempty_ball.mpr hδ') hball_zero
  have hKA_ne : (K ∩ A).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsub : K ⊆ Aᶜ := fun x hx hxA => by
      have : x ∈ K ∩ A := ⟨hx, hxA⟩
      rw [hempty] at this; exact this
    exact hK_ne_zero (le_antisymm ((measure_mono hsub).trans hA.le) bot_le)
  obtain ⟨x, hxK, hxA⟩ := hKA_ne
  obtain ⟨hp_ball, hmax⟩ := hP_spec x hxK
  exact ⟨P x, ball_subset_ball hδ'_le hp_ball, x, hxK.1, hxA, hmax⟩

end LocalJensen
end BMCompactPDE
#print axioms BMCompactPDE.exists_local_subgradient
#print axioms BMCompactPDE.jensen_lemma_exists_good_maximizer
