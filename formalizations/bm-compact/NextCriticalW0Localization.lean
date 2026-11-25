import UpstreamBoundaryExcess

/-! Genuine off-obstacle localization of an actual W0 graph. A compact
smooth cutoff vanishes in a neighborhood of K; both actual function and
supplied gradient are zero on the cutoff region. Smooth W0 approximants then
become actual compact tests outside K, with both Lp limits proved. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem nextCritical_bounded_scalar_multiplier_limit {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ} {μ : Measure (Space n)}
    {a : Space n → ℝ} {C : ℝ} (hC : 0≤C) (ha : ∀ x,‖a x‖≤C)
    {f : ℕ → Space n → E}
    (hl : Tendsto (fun j=>eLpNorm (f j) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun j=>eLpNorm (fun x=>a x • f j x) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul hl (Or.inr (by simp : ‖C‖ₑ≠(∞:ℝ≥0∞)))
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
  intro j
  dsimp only
  rw [←eLpNorm_const_smul]
  exact eLpNorm_mono (fun x=>by
    simp only [norm_smul,Pi.smul_apply,Real.norm_eq_abs,abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _))

set_option maxHeartbeats 1400000 in
theorem ZeroBoundarySobolevPair.off_compact_of_zero_on_open_neighborhood
    {n : ℕ} {p : ℝ} {O K N : Set (Space n)} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K⊆O) (hN : IsOpen N) (hKN : K⊆N)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g)
    (hz : ∀ᵐ x ∂volume.restrict O,x∈N → u x=0 ∧ g x=0) :
    ZeroBoundarySobolevPair p (O\K) u g := by
  have hp : 1<p := hu.1.1
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let μ := volume.restrict O
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK (hN.inter hO)
    (fun x hx=>⟨hKN hx,hKO hx⟩)
  let β : Space n → ℝ := fun x=>Real.smoothTransition (2*a x)
  have hβ : SmoothTest (N∩O) β := by
    refine ⟨Real.smoothTransition.contDiff.comp (contDiff_const.mul ha.1),
      ha.2.1.mul_left.comp_left (Real.smoothTransition.zero_of_nonpos le_rfl),?_⟩
    exact (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) (fun x=>2*a x)).trans
      (tsupport_mul_subset_right.trans ha.2.2.1)
  have hβ0 (x : Space n) : 0≤β x := Real.smoothTransition.nonneg _
  have hβ1 (x : Space n) : β x≤1 := Real.smoothTransition.le_one _
  let χ : Space n → ℝ := fun x=>1-β x
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.sub hβ.1
  have hχC (x : Space n) : ‖χ x‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hβ1 x))]
    exact sub_le_self _ (hβ0 x)
  have hχK (x : Space n) (hx : x∈K) : χ=ᶠ[𝓝 x] (fun _=>(0:ℝ)) := by
    have hxA : (1:ℝ)/2<a x := by linarith only [ha.2.2.2 x hx]
    have ht := ha.1.continuous.continuousAt.tendsto.eventually (eventually_gt_nhds hxA)
    filter_upwards [ht] with y hy
    have hh : 1≤2*a y := by linarith only [hy]
    simp only [χ,β,Real.smoothTransition.one_of_one_le hh,sub_self]
  have hgradχ (x : Space n) : gradient χ x= -gradient β x := by
    have hh := gradient_fun_sub (u:=fun _ : Space n=> (1:ℝ)) (v:=β)
      (differentiable_const (1:ℝ)) (hβ.1.differentiable (by simp)) x
    simpa only [gradient_fun_const,zero_sub,χ] using hh
  have hχout (x : Space n) (hx : x∉N) : χ x=1 ∧ gradient χ x=0 := by
    have hxt : x∉tsupport β := fun ht=>hx ((hβ.2.2 ht).1)
    have hb0 := image_eq_zero_of_notMem_tsupport hxt
    have hbg0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hxt
    simp only [χ,hb0,sub_zero,hgradχ,hbg0,neg_zero,and_self]
  obtain ⟨A0,hA0⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hβ.2.1).exists_bound_of_continuous
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hβ.1)
  let A : ℝ := max A0 0
  have hA : 0≤A := le_max_right _ _
  have hgA (x : Space n) : ‖gradient χ x‖≤A := by
    rw [hgradχ,norm_neg]
    exact (hA0 x).trans (le_max_left _ _)
  obtain ⟨φ,hφ,hLu,hLg⟩ := hu.2
  let ψ : ℕ → Space n → ℝ := fun j x=>χ x*φ j x
  have hψ (j : ℕ) : SmoothTest (O\K) (ψ j) := by
    refine ⟨hχ.mul (hφ j).1,(hφ j).2.1.mul_left,?_⟩
    intro x hx
    refine ⟨(tsupport_mul_subset_right.trans (hφ j).2.2) hx,?_⟩
    intro hxK
    have heq : ψ j=ᶠ[𝓝 x] (0 : Space n → ℝ) := by
      filter_upwards [hχK x hxK] with y hy
      simp only [ψ,hy,zero_mul,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hx
  have hφs (j : ℕ) := (hφ j).sobolevPair hp
  have hU := nextCritical_bounded_scalar_multiplier_limit (μ:=μ) (p:=p) (by norm_num : (0:ℝ)≤1) hχC hLu
  have hG := nextCritical_bounded_scalar_multiplier_limit (μ:=μ) (p:=p) (by norm_num : (0:ℝ)≤1) hχC hLg
  have hE : Tendsto (fun j=>eLpNorm (fun x=>(φ j x-u x) • gradient χ x) q μ) atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul hLu (Or.inr (by simp : ‖A‖ₑ≠(∞:ℝ≥0∞)))
    simp only [mul_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
    intro j
    dsimp only
    rw [←eLpNorm_const_smul]
    apply eLpNorm_mono
    intro x
    simp only [norm_smul,Pi.smul_apply,Real.norm_eq_abs,abs_of_nonneg hA]
    exact (mul_le_mul_of_nonneg_left (hgA x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hψu : Tendsto (fun j=>eLpNorm (ψ j-u) q μ) atTop (𝓝 0) := by
    apply hU.congr'
    exact Eventually.of_forall (fun j=>eLpNorm_congr_ae (by
      filter_upwards [hz] with x hx
      change χ x*(φ j x-u x)=χ x*φ j x-u x
      by_cases hxN : x∈N
      · rw [(hx hxN).1];ring
      · rw [(hχout x hxN).1];ring))
  have hψg : Tendsto (fun j=>eLpNorm (fun x=>gradient (ψ j) x-g x) q μ) atTop (𝓝 0) := by
    have ht := hG.add hE
    simp only [add_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
    intro j
    have heq : (fun x=>gradient (ψ j) x-g x)=ᵐ[μ]
        (fun x=>χ x • (gradient (φ j) x-g x)+(φ j x-u x) • gradient χ x) := by
      filter_upwards [hz] with x hx
      have hh := gradient_fun_mul_actual (hχ.differentiable (by simp) x) ((hφ j).1.differentiable (by simp) x)
      change gradient (ψ j) x=χ x • gradient (φ j) x+φ j x • gradient χ x at hh
      rw [hh]
      by_cases hxN : x∈N
      · rw [(hx hxN).1,(hx hxN).2];module
      · rw [(hχout x hxN).1,(hχout x hxN).2];module
    dsimp only
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_add_le (hχ.continuous.aestronglyMeasurable.smul ((hφs j).2.2.1.sub hu.1.2.2.1).1)
      (((hφs j).2.1.sub hu.1.2.1).1.smul
        (BMCompactCapacityV2.continuous_gradient_of_contDiff hχ).aestronglyMeasurable)
      (ENNReal.one_le_ofReal.mpr hp.le)
  have hSobD := hu.1.mono_actual (sdiff_subset : O\K⊆O)
  apply zeroBoundarySobolevPair_of_eLpNorm_limits hp
    (fun j=>(hψ j).zeroBoundarySobolevPair hp) hSobD.2.1 hSobD.2.2.1
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hψu (fun _=>bot_le)
      (fun _=>eLpNorm_mono_measure _ (Measure.restrict_mono_set volume sdiff_subset))
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hψg (fun _=>bot_le)
      (fun _=>eLpNorm_mono_measure _ (Measure.restrict_mono_set volume sdiff_subset))

end BMCompactPDE
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.off_compact_of_zero_on_open_neighborhood
