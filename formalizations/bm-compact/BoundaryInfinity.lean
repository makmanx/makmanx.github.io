import BoundaryPointwise
import ContinuousUniformSmallTail
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Genuine vanishing at infinity for the selected variational p-capacity
potential. The only approximation input in the intermediate theorem is
compact-support Lq approximation; the final existence theorem constructs
that data through the already checked capacity minimization. No infinity
limit, boundary trace, C1 or Green normalization is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem boundary_continuous_le_of_ae {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {C : ℝ} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hb : ∀ᵐ x ∂volume.restrict Ω,u x≤C) : ∀ x∈Ω,u x≤C := by
  have hae : (fun x => max (u x-C) 0) =ᵐ[volume.restrict Ω] (fun _ => 0) := by
    filter_upwards [hb] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have he := Measure.eqOn_open_of_ae_eq hae hΩ
    ((show Continuous (fun r : ℝ => max (r-C) 0) by fun_prop).comp_continuousOn hu)
    continuousOn_const
  intro x hx
  exact sub_nonpos.mp ((le_max_left (u x-C) 0).trans_eq (he hx))

set_option maxHeartbeats 800000 in
private theorem boundary_eventually_upper {n : ℕ} {p q : ℝ}
    {K : Set (Space n)} (hK : IsCompact K) (hpn : p<(n : ℝ)) (hpq : p≤q)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Kᶜ u g) (hcont : ContinuousOn u Kᶜ)
    (huq : MemLp u (ENNReal.ofReal q) volume)
    {φ : ℕ → Space n → ℝ} (hφc : ∀ j,Continuous (φ j))
    (hφK : ∀ j,HasCompactSupport (φ j))
    (hlim : Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ a in cocompact (Space n),u a≤ε := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hq0 : 0<q := hp0.trans_le hpq
  obtain ⟨G,hG,hcut⟩ := exists_uniform_scaled_cutoff n
  obtain ⟨θ,hθ,hsmall⟩ := exists_uniform_source_small_tail_threshold hu.1
    (le_refl (0 : ℝ)) hG.le hpn
  let α : ℝ := 1/p-1/q
  have hα : 0≤α := by
    dsimp only [α]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp0 hpq)
  let C : ℝ≥0∞ := (volume (ball (0 : Space n) 3))^α
  have hV : volume (ball (0 : Space n) 3)≠(∞ : ℝ≥0∞) :=
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (isCompact_closedBall (0 : Space n) 3).measure_lt_top).ne
  have hC : C≠(∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg hα hV
  let F : ℕ → ℝ≥0∞ := fun j => ‖ε⁻¹‖ₑ*eLpNorm (φ j-u) (ENNReal.ofReal q) volume*C
  have hFlim : Tendsto F atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul (a:=‖ε⁻¹‖ₑ) hlim (Or.inr enorm_ne_top)
    rw [mul_zero] at ht
    simpa only [zero_mul,F] using ENNReal.Tendsto.mul_const ht (Or.inr hC)
  obtain ⟨j,hj⟩ := (hFlim.eventually
    (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hθ))).exists
  obtain ⟨B,hB⟩ := (hK.union (hφK j)).isBounded.subset_ball (0 : Space n)
  have houtside (a : Space n) (ha : B+4<‖a‖) :
      ∀ y∈closedBall a 3,y∉K ∧ y∉tsupport (φ j) := by
    intro y hy
    have hdist : dist a y≤3 := by simpa only [mem_closedBall,dist_comm] using hy
    have hn (hmem : y∈K ∪ tsupport (φ j)) : False := by
      have hyB : ‖y‖<B := by simpa only [mem_ball,dist_zero_right] using hB hmem
      have ht : ‖a‖≤3+‖y‖ := by
        calc ‖a‖=dist a 0 := (dist_zero_right a).symm
             _≤dist a y+dist y 0 := dist_triangle a y 0
             _≤3+‖y‖ := by rw [dist_zero_right]; linarith only [hdist]
      linarith only [ha,hyB,ht]
    exact ⟨fun hyK => hn (Or.inl hyK),fun hyφ => hn (Or.inr hyφ)⟩
  filter_upwards [(isCompact_closedBall (0 : Space n) (B+4)).compl_mem_cocompact] with a ha
  have ha' : B+4<‖a‖ := by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using ha
  let D := ball a (3 : ℝ)
  have hD : LocalDomain D Kᶜ := ⟨isOpen_ball,isBounded_ball,fun y hy =>
    (houtside a ha' y (closure_ball_subset_closedBall hy)).1⟩
  obtain ⟨η,hη,hη0,hη1,hηeq,_,hηg⟩ := hcut a 1 zero_lt_one
  have hηtest : SmoothTest D η := by simpa only [mul_one] using hη
  have hηgrad : ∀ x∈D,‖gradient η x‖≤G := by
    intro x _
    simpa only [div_one] using hηg x
  let w : Space n → ℝ := ε⁻¹ • u
  let b : Space n → Space n := ε⁻¹ • g
  have hw : WeakPSourceSubsolutionPair p 0 Kᶜ w b := (hu.smul ε⁻¹).source_zero.subsolution
  have herr : AEStronglyMeasurable (u-φ j) volume :=
    huq.1.sub (hφc j).aestronglyMeasurable
  have hlocal : eLpNorm' (fun x => max (w x) 0) p (volume.restrict D)≤F j := by
    have hφzero (x : Space n) (hx : x∈D) : φ j x=0 :=
      image_eq_zero_of_notMem_tsupport ((houtside a ha' x (ball_subset_closedBall hx)).2)
    have hmono : eLpNorm' (fun x => max (w x) 0) p (volume.restrict D)≤
        eLpNorm' (ε⁻¹ • (u-φ j)) p (volume.restrict D) := by
      apply eLpNorm'_mono_ae hp0.le
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      change ‖max (ε⁻¹*u x) 0‖≤‖ε⁻¹*(u x-φ j x)‖
      rw [hφzero x hx,sub_zero]
      change |max (ε⁻¹*u x) 0|≤|ε⁻¹*u x|
      rw [abs_of_nonneg (le_max_right (ε⁻¹*u x) (0 : ℝ))]
      exact max_le (le_abs_self _) (abs_nonneg _)
    have hcmp := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ:=volume.restrict D) hp0 hpq
      ((herr.mono_measure Measure.restrict_le_self).const_smul ε⁻¹)
    have heq : (volume.restrict D) univ=volume (ball (0 : Space n) 3) := by
      simp only [Measure.restrict_apply_univ,D]
      exact Measure.addHaar_ball_center volume a 3
    rw [eLpNorm'_const_smul ε⁻¹ hq0,heq] at hcmp
    have hmeasure : eLpNorm' (u-φ j) q (volume.restrict D)≤
        eLpNorm (φ j-u) (ENNReal.ofReal q) volume := by
      rw [eLpNorm_sub_comm,eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq0)
        ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hq0.le]
      exact eLpNorm'_mono_measure _ Measure.restrict_le_self hq0.le
    exact hmono.trans (hcmp.trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmeasure zero_le) zero_le))
  have hsmallnorm : (eLpNorm' (fun x => max (w x) 0) p (volume.restrict D)).toReal≤θ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlocal.trans hj.le)
    simpa only [ENNReal.toReal_ofReal hθ.le] using hh
  have hae := hsmall Kᶜ D η hD hηtest hη0 hη1 hηgrad 0 w b le_rfl hw hsmallnorm
  have hAE : ∀ᵐ x ∂volume.restrict (ball a (1 : ℝ)),u x≤ε := by
    have ht := ae_restrict_of_ae_restrict_of_subset
      (show ball a (1 : ℝ)⊆D by exact ball_subset_ball (by norm_num)) hae
    filter_upwards [ht,ae_restrict_mem measurableSet_ball] with x hx hxB
    have hηx : η x=1 := by simpa only [mul_one] using hηeq x (ball_subset_closedBall hxB)
    have hs := mul_le_mul_of_nonneg_left (hx hηx) hε.le
    simpa only [w,Pi.smul_apply,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ hε.ne',one_mul,mul_one] using hs
  have hBC : ball a (1 : ℝ)⊆Kᶜ :=
    (ball_subset_ball (by norm_num : (1 : ℝ)≤3)).trans (subset_closure.trans hD.2.2)
  exact boundary_continuous_le_of_ae isOpen_ball (hcont.mono hBC) hAE a (mem_ball_self zero_lt_one)

/-- The infinity-zero condition is derived from the genuine weak equation and
actual compact Lq approximation; it is not a boundary or normalization input. -/
theorem WeakPHarmonicPair.tendsto_zero_at_infinity_of_compact_lp_approximation
    {n : ℕ} {p q : ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hpn : p<(n : ℝ)) (hpq : p≤q) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Kᶜ u g) (hcont : ContinuousOn u Kᶜ)
    (huq : MemLp u (ENNReal.ofReal q) volume) (hpos : ∀ x∈Kᶜ,0≤u x)
    {φ : ℕ → Space n → ℝ} (hφc : ∀ j,Continuous (φ j))
    (hφK : ∀ j,HasCompactSupport (φ j))
    (hlim : Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal q) volume) atTop (𝓝 0)) :
    Tendsto u (cocompact (Space n)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := boundary_eventually_upper hK hpn hpq hu hcont huq hφc hφK hlim (half_pos hε)
  filter_upwards [he,hK.compl_mem_cocompact] with x hx hxK
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (hpos x hxK)]
  exact hx.trans_lt (half_lt_self hε)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.tendsto_zero_at_infinity_of_compact_lp_approximation
