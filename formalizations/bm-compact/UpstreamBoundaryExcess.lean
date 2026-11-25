import CapacityBoundaryAtInfinity
import RootCompactSobolevDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual obstacle boundary tests from genuine capacity-admissible approximation.
No pointwise trace or boundary continuity is an input. Strict smooth barrier
excesses are approximated by tests supported away from the compact obstacle. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_restrict_limit {n : ℕ} {p : ℝ} {O D : Set (Space n)}
    (hDO : D⊆O) {v : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (ht : Tendsto (fun j => eLpNorm (v j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (v j-u) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
    (fun _=>eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hDO))

private theorem upstream_positivePart_off_obstacle_of_smooth_limits
    {n : ℕ} {p : ℝ} {O K : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : ZeroBoundarySobolevPair p O v h)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,SmoothTest O (φ j))
    (hφK : ∀ j x,x∈K → ∀ᶠ y in 𝓝 x,φ j y≤0)
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-v) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-h x)
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0)) :
    ZeroBoundarySobolevPair p (O\K) (fun x=>max (v x) 0) (positivePartGradient v h) := by
  let D := O\K
  let μ := volume.restrict D
  let q := ENNReal.ofReal p
  have hp : 1<p := hv.1.1
  have hq0 : q≠0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqt : q≠(∞:ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hlimuD := upstream_restrict_limit (sdiff_subset : D⊆O) hlimu
  have hlimgD : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-h x) q μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimg (fun _=>bot_le)
      (fun j=>eLpNorm_mono_measure _ (Measure.restrict_mono_set volume sdiff_subset))
  have hsd := hv.1.mono_actual (sdiff_subset : D⊆O)
  have hφs (j : ℕ) := (hφ j).sobolevPair hp |>.mono_actual (sdiff_subset : D⊆O)
  have hmeas (j : ℕ) : AEStronglyMeasurable (φ j) μ := (hφs j).2.1.1
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm hq0 hmeas hsd.2.1.1 hlimuD
  obtain ⟨σ,hσ,hσlim⟩ := hmeasure.exists_seq_tendsto_ae
  obtain ⟨C,hC,hbound⟩ := positivePartSlope_uniform_bound
  have hC0 : 0≤C := zero_le_one.trans hC
  have hsmooth (k : ℕ) : ZeroBoundarySobolevPair p D
      (fun x=>smoothPositivePart k (v x)) (fun x=>positivePartSlope k (v x) • h x) := by
    let ψ : ℕ → Space n → ℝ := fun j x=>smoothPositivePart k (φ (σ j) x)
    have hψ (j : ℕ) : SmoothTest D (ψ j) := by
      have hz : smoothPositivePart k 0=0 := smoothPositivePart_eq_zero_of_nonpos k le_rfl
      refine ⟨(smoothPositivePart_contDiff k).comp (hφ (σ j)).1,
        (hφ (σ j)).2.1.comp_left hz,?_⟩
      intro x hx
      refine ⟨(tsupport_comp_subset hz (φ (σ j))).trans (hφ (σ j)).2.2 hx,?_⟩
      intro hxK
      have hn : ∀ᶠ y in 𝓝 x,φ (σ j) y≤0 := hφK (σ j) x hxK
      have he : ψ j=ᶠ[𝓝 x] (0 : Space n → ℝ) := by
        filter_upwards [hn] with y hy
        exact smoothPositivePart_eq_zero_of_nonpos k hy
      exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
    have hs := (hv.smoothPositivePart k).1.mono_actual (sdiff_subset : D⊆O)
    apply zeroBoundarySobolevPair_of_eLpNorm_limits hp
      (fun j=>(hψ j).zeroBoundarySobolevPair hp) hs.2.1 hs.2.2.1
    · have hb (j : ℕ) : eLpNorm (ψ j-(fun x=>smoothPositivePart k (v x))) q μ≤
          ‖C‖ₑ*eLpNorm (φ (σ j)-v) q μ := by
        rw [←eLpNorm_const_smul]
        apply eLpNorm_mono
        intro x
        simpa only [ψ,Pi.sub_apply,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC0] using
          smoothPositivePart_norm_sub_le k (hbound k) (φ (σ j) x) (v x)
      have ht := ENNReal.Tendsto.const_mul (hlimuD.comp hσ.tendsto_atTop) (Or.inr (by simp : ‖C‖ₑ≠(∞:ℝ≥0∞)))
      simp only [mul_zero] at ht
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le) hb
    · have hgrad (j : ℕ) : gradient (ψ j)=
          fun x=>positivePartSlope k (φ (σ j) x) • gradient (φ (σ j)) x := by
        funext x
        exact gradient_smoothPositivePart_comp ((hφ (σ j)).1.differentiable (by simp)) k x
      simp_rw [hgrad]
      apply tendsto_eLpNorm_bounded_smul hq0 hqt hq hC0
        (fun j=>(continuous_positivePartSlope k).comp_aestronglyMeasurable (hmeas (σ j)))
        ((continuous_positivePartSlope k).comp_aestronglyMeasurable hsd.2.1.1)
        (fun j=>(hφs (σ j)).2.2.1) hsd.2.2.1
        (fun j x=>hbound k (φ (σ j) x)) (fun x=>hbound k (v x))
      · filter_upwards [hσlim] with x hx
        exact (continuous_positivePartSlope k).continuousAt.tendsto.comp hx
      · exact hlimgD.comp hσ.tendsto_atTop
  have hpos := hv.positivePart.1.mono_actual (sdiff_subset : D⊆O)
  apply zeroBoundarySobolevPair_of_eLpNorm_limits hp hsmooth hpos.2.1 hpos.2.2.1
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b:=(2:ℝ) • v)
    · intro j
      exact (hsmooth j).1.2.1.1.sub hpos.2.1.1
    · exact hsd.2.1.const_smul (2:ℝ)
    · intro j
      exact Eventually.of_forall (fun x=>by
        have hn : ‖max (v x) 0‖≤‖v x‖ := by
          by_cases hx : v x≤0
          · simp [max_eq_right hx]
          · rw [max_eq_left (lt_of_not_ge hx).le]
        calc
          ‖smoothPositivePart j (v x)-max (v x) 0‖≤‖smoothPositivePart j (v x)‖+‖max (v x) 0‖ := norm_sub_le _ _
          _≤‖v x‖+‖v x‖ := add_le_add (smoothPositivePart_norm_le j _) hn
          _=‖((2:ℝ) • v) x‖ := by simp [norm_smul];ring)
    · exact Eventually.of_forall (fun x=>tendsto_const_nhds.congr'
        ((smoothPositivePart_eventually_eq (v x)).mono (fun j hj=>by simp only [Pi.sub_apply,hj,sub_self])))
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b:=(C+1) • h)
    · intro j
      exact (hsmooth j).1.2.2.1.1.sub hpos.2.2.1.1
    · exact hsd.2.2.1.const_smul (C+1)
    · intro j
      exact Eventually.of_forall (fun x=>by
        have hn : ‖positivePartGradient v h x‖≤‖h x‖ := positivePartGradient_norm_le v h x
        calc
          ‖positivePartSlope j (v x) • h x-positivePartGradient v h x‖≤‖positivePartSlope j (v x) • h x‖+‖positivePartGradient v h x‖ := norm_sub_le _ _
          _≤C*‖h x‖+‖h x‖ := by
            rw [norm_smul]
            exact add_le_add (mul_le_mul_of_nonneg_right (hbound j _) (norm_nonneg _)) hn
          _=‖((C+1) • h) x‖ := by
            simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤C+1)]
            ring)
    · exact Eventually.of_forall (fun x=>by
        apply tendsto_const_nhds.congr'
        filter_upwards [positivePartSlope_eventually_eq (v x)] with j hj
        rw [hj]
        split_ifs <;> simp)

private theorem upstream_bounded_scalar_multiplier_limit {n : ℕ} {E : Type*}
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

/- Genuine localized strict barrier excess is an actual W0 test off the
compact obstacle, derived from actual admissible scalar/gradient approximants.
The displayed field is the actual product/difference weak gradient. -/
set_option maxHeartbeats 1200000 in
theorem capacity_admissible_local_excess_zeroBoundary
    {n : ℕ} {p : ℝ} {O K : Set (Space n)} (hO : IsOpen O)
    {u : Space n → ℝ} {g : Space n → Space n} (hu : SobolevPair p O u g)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K univ (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x)
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    {χ b : Space n → ℝ} (hχ : SmoothTest O χ) (hχ0 : ∀ x,0≤χ x)
    (hb : ContDiff ℝ ∞ b) (hbK : ∀ x∈K,b x≤1) {ε : ℝ} (hε : 0<ε) :
    ZeroBoundarySobolevPair p (O\K)
      (fun x=>max (χ x*(b x-u x-ε)) 0)
      (positivePartGradient (fun x=>χ x*(b x-u x-ε))
        (fun x=>gradient (fun y=>χ y*(b y-ε)) x-(χ x • g x+u x • gradient χ x))) := by
  let μ := volume.restrict O
  let q := ENNReal.ofReal p
  let γ : Space n → ℝ := fun x=>χ x*(b x-ε)
  let v : Space n → ℝ := fun x=>γ x-χ x*u x
  let G : Space n → Space n := fun x=>gradient γ x-(χ x • g x+u x • gradient χ x)
  let ψ : ℕ → Space n → ℝ := fun j x=>γ x-χ x*φ j x
  have hγ : SmoothTest O γ := ⟨hχ.1.mul (hb.sub contDiff_const),
    hχ.2.1.mul_right,tsupport_mul_subset_left.trans hχ.2.2⟩
  have hprod := hu.mul_smooth_compactSupport_zeroBoundary hO hχ.1 hχ.2.1 hχ.2.2
  have hv : ZeroBoundarySobolevPair p O v G := (hγ.zeroBoundarySobolevPair hu.1).sub_actual hprod
  have hψ (j : ℕ) : SmoothTest O (ψ j) := by
    refine ⟨hγ.1.sub (hχ.1.mul (hφ j).1),hγ.2.1.sub hχ.2.1.mul_right,?_⟩
    exact (tsupport_sub _ _).trans (union_subset hγ.2.2 (tsupport_mul_subset_left.trans hχ.2.2))
  have hψK (j : ℕ) (x : Space n) (hx : x∈K) : ∀ᶠ y in 𝓝 x,ψ j y≤0 := by
    have hstrict : b x-φ j x-ε<0 := by linarith only [hbK x hx,(hφ j).2.2.2 x hx,hε]
    have he := (((hb.continuous.sub (hφ j).1.continuous).sub continuous_const).continuousAt.tendsto.eventually
      (eventually_lt_nhds hstrict))
    filter_upwards [he] with y hy
    have heq : ψ j y=χ y*(b y-φ j y-ε) := by dsimp only [ψ,γ];ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (hχ0 y) hy.le
  obtain ⟨C0,hC0bound⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  let C := max C0 0
  have hC : 0≤C := le_max_right _ _
  have hχC (x : Space n) : ‖χ x‖≤C := (hC0bound x).trans (le_max_left _ _)
  obtain ⟨A0,hA0bound⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1).exists_bound_of_continuous
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hχ.1)
  let A := max A0 0
  have hA : 0≤A := le_max_right _ _
  have hgradA (x : Space n) : ‖gradient χ x‖≤A := (hA0bound x).trans (le_max_left _ _)
  have hU := upstream_bounded_scalar_multiplier_limit hC hχC hlimu
  have hE := upstream_bounded_scalar_multiplier_limit hC hχC hlimg
  have hB : Tendsto (fun j=>eLpNorm (fun x=>(φ j x-u x) • gradient χ x) q μ) atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul hlimu (Or.inr (by simp : ‖A‖ₑ≠(∞:ℝ≥0∞)))
    simp only [mul_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
    intro j
    dsimp only
    rw [←eLpNorm_const_smul]
    apply eLpNorm_mono
    intro x
    simp only [norm_smul,Pi.smul_apply,Real.norm_eq_abs,abs_of_nonneg hA]
    exact (mul_le_mul_of_nonneg_left (hgradA x) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hψu : Tendsto (fun j=>eLpNorm (ψ j-v) q μ) atTop (𝓝 0) := by
    convert hU using 1
    funext j
    have heq : ψ j-v=-(fun x=>χ x • (φ j-u) x) := by
      funext x
      simp only [ψ,v,Pi.sub_apply,Pi.neg_apply,smul_eq_mul]
      ring
    rw [heq,eLpNorm_neg]
  have hφs (j : ℕ) : SobolevPair p O (φ j) (gradient (φ j)) :=
    (show SmoothTest univ (φ j) from ⟨(hφ j).1,(hφ j).2.1,subset_univ _⟩).sobolevPair hu.1 |>.mono_actual (subset_univ O)
  have hψg : Tendsto (fun j=>eLpNorm (fun x=>gradient (ψ j) x-G x) q μ) atTop (𝓝 0) := by
    have ht := hE.add hB
    simp only [add_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
    intro j
    have heq : (fun x=>gradient (ψ j) x-G x)=-(fun x=>χ x • (gradient (φ j) x-g x)+(φ j x-u x) • gradient χ x) := by
      funext x
      have hgψ := gradient_fun_sub (hγ.1.differentiable (by simp))
        ((hχ.1.mul (hφ j).1).differentiable (by simp)) x
      change gradient (ψ j) x=gradient γ x-gradient (fun y=>χ y*φ j y) x at hgψ
      rw [hgψ,gradient_fun_mul_actual (hχ.1.differentiable (by simp) x) ((hφ j).1.differentiable (by simp) x)]
      simp only [G,Pi.neg_apply]
      module
    dsimp only
    rw [heq,eLpNorm_neg]
    have hmχ := hχ.1.continuous.aestronglyMeasurable (μ:=μ)
    have hmgχ := (BMCompactCapacityV2.continuous_gradient_of_contDiff hχ.1).aestronglyMeasurable (μ:=μ)
    exact eLpNorm_add_le (hmχ.smul ((hφs j).2.2.1.sub hu.2.2.1).1)
      (((hφs j).2.1.sub hu.2.1).1.smul hmgχ) (ENNReal.one_le_ofReal.mpr hu.1.le)
  have hw := upstream_positivePart_off_obstacle_of_smooth_limits hv hψ hψK hψu hψg
  have heq : v=(fun x=>χ x*(b x-u x-ε)) := by funext x;dsimp only [v,γ];ring
  simpa only [heq,G,γ] using hw

end BMCompactPDE
#print axioms BMCompactPDE.capacity_admissible_local_excess_zeroBoundary
