import UpstreamBoundaryExcess

/-! A genuine W0 ideal property. Subtracting a nonnegative actual Sobolev
barrier and a nonnegative constant, then taking the positive part, preserves
W0. Smooth W0 approximation and two successive actual graph limits derive
admissibility. Neither barrier continuity nor a trace/ideal axiom is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem next_ideal_difference_sobolev
    {n : ℕ} {p ε : ℝ} {O : Set (Space n)} (hOb : Bornology.IsBounded O)
    {u B : Space n → ℝ} {g b : Space n → Space n}
    (hu : SobolevPair p O u g) (hB : SobolevPair p O B b) :
    SobolevPair p O (fun x=>u x-B x-ε) (g-b) := by
  have hs := (hu.add (hB.smul (-1))).add (sobolevPair_const hu.1 hOb (-ε))
  apply hs.congr (Eventually.of_forall (fun x=>by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring))
  exact Eventually.of_forall (fun x=>by
    simp only [Pi.add_apply,Pi.smul_apply,Pi.zero_apply,add_zero,neg_one_smul,sub_eq_add_neg])

private theorem next_ideal_smooth_compact_approx
    {n : ℕ} {p ε : ℝ} {O : Set (Space n)} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) {f B : Space n → ℝ} {b : Space n → Space n}
    (hf : SmoothTest O f) (hB : SobolevPair p O B b)
    (hB0 : ∀ x∈O,0≤B x) (hε : 0≤ε) (k : ℕ) :
    ZeroBoundarySobolevPair p O (fun x=>BMCompactPDE.smoothPositivePart k (f x-B x-ε))
      (fun x=>positivePartSlope k (f x-B x-ε) • (gradient f x-b x)) := by
  let K := tsupport f
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hf.2.1.isCompact hO hf.2.2
  let χ : Space n → ℝ := fun x=>Real.smoothTransition (a x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp ha.1
  have hχc : HasCompactSupport χ := ha.2.1.comp_left (Real.smoothTransition.zero_of_nonpos le_rfl)
  have hχs : tsupport χ⊆O := (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) a).trans ha.2.2.1
  have hχ0 (x : Space n) : 0≤χ x := Real.smoothTransition.nonneg _
  have hχ1 (x : Space n) (hx : x∈K) : χ x=1 := Real.smoothTransition.one_of_one_le (ha.2.2.2 x hx)
  have hχg (x : Space n) (hx : x∈K) : gradient χ x=0 := by
    have hm : IsLocalMax χ x := Eventually.of_forall (fun y=>by
      rw [hχ1 x hx]
      exact Real.smoothTransition.le_one _)
    unfold gradient
    rw [hm.fderiv_eq_zero]
    exact map_zero _
  let S : Space n → ℝ := fun x=>f x-B x-ε
  let G : Space n → Space n := fun x=>gradient f x-b x
  have hs : SobolevPair p O S G := next_ideal_difference_sobolev hOb (hf.sobolevPair hB.1) hB
  have ht := (hs.mul_smooth_compactSupport_zeroBoundary hO hχ hχc hχs).smoothPositivePart k
  have hpos (x : Space n) (hxO : x∈O) (hx : 0<S x) : x∈K := by
    by_contra hn
    have hz : f x=0 := image_eq_zero_of_notMem_tsupport hn
    dsimp only [S] at hx
    linarith only [hx,hz,hB0 x hxO,hε]
  apply ht.congr
  · filter_upwards [ae_restrict_mem hO.measurableSet] with x hxO
    by_cases hx : 0<S x
    · simp only [hχ1 x (hpos x hxO hx),one_mul,S]
    · have hS : S x≤0 := le_of_not_gt hx
      have hχS : χ x*S x≤0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hS
      exact (smoothPositivePart_eq_zero_of_nonpos k hχS).trans
        (smoothPositivePart_eq_zero_of_nonpos k hS).symm
  · filter_upwards [ae_restrict_mem hO.measurableSet] with x hxO
    by_cases hx : 0<S x
    · simp only [hχ1 x (hpos x hxO hx),hχg x (hpos x hxO hx),one_mul,one_smul,smul_zero,add_zero,S,G,Pi.sub_apply]
    · have hS : S x≤0 := le_of_not_gt hx
      have hχS : χ x*S x≤0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hS
      simp only [positivePartSlope_eq_zero_of_nonpos k hχS,positivePartSlope_eq_zero_of_nonpos k hS,zero_smul,S,G,Pi.sub_apply]

set_option maxHeartbeats 1800000 in
/-- A genuine Sobolev lattice ideal property, derived from actual smooth W0
approximants. B is only Sobolev and nonnegative on the bounded open domain;
no continuity, boundary trace or desired W0 membership is assumed. -/
theorem ZeroBoundarySobolevPair.positivePart_sub_nonnegative_sobolev
    {n : ℕ} {p ε : ℝ} {O : Set (Space n)} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) {u B : Space n → ℝ} {g b : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g) (hB : SobolevPair p O B b)
    (hB0 : ∀ x∈O,0≤B x) (hε : 0≤ε) :
    ZeroBoundarySobolevPair p O (fun x=>max (u x-B x-ε) 0)
      (positivePartGradient (fun x=>u x-B x-ε) (g-b)) := by
  obtain ⟨su,φ,hφ,hLu,hLg⟩ := hu
  let μ := volume.restrict O
  let q := ENNReal.ofReal p
  let S : Space n → ℝ := fun x=>u x-B x-ε
  let G : Space n → Space n := g-b
  have hp : 1<p := su.1
  have hq0 : q≠0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hs : SobolevPair p O S G := next_ideal_difference_sobolev hOb su hB
  have hφS (j : ℕ) : SobolevPair p O (fun x=>φ j x-B x-ε) (gradient (φ j)-b) :=
    next_ideal_difference_sobolev hOb ((hφ j).sobolevPair hp) hB
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm hq0
    (fun j=>((hφ j).sobolevPair hp).2.1.1) su.2.1.1 hLu
  obtain ⟨σ,hσ,hσlim⟩ := hmeasure.exists_seq_tendsto_ae
  obtain ⟨C,hC,hbound⟩ := positivePartSlope_uniform_bound
  have hC0 : 0≤C := zero_le_one.trans hC
  have hSmooth (k : ℕ) : ZeroBoundarySobolevPair p O
      (fun x=>BMCompactPDE.smoothPositivePart k (S x)) (fun x=>positivePartSlope k (S x) • G x) := by
    have hscalar : MemLp (fun x=>BMCompactPDE.smoothPositivePart k (S x)) q μ :=
      hs.2.1.of_le ((smoothPositivePart_contDiff k).continuous.comp_aestronglyMeasurable hs.2.1.1)
        (Eventually.of_forall (fun x=>smoothPositivePart_norm_le k (S x)))
    have hgradmeas : AEStronglyMeasurable (fun x=>positivePartSlope k (S x) • G x) μ :=
      ((continuous_positivePartSlope k).comp_aestronglyMeasurable hs.2.1.1).smul hs.2.2.1.1
    have hgrad : MemLp (fun x=>positivePartSlope k (S x) • G x) q μ :=
      (hs.2.2.1.const_smul C).of_le hgradmeas (Eventually.of_forall (fun x=>by
        simp only [norm_smul,Pi.smul_apply,Real.norm_eq_abs,abs_of_nonneg hC0]
        exact mul_le_mul_of_nonneg_right (hbound k (S x)) (norm_nonneg _)))
    apply zeroBoundarySobolevPair_of_eLpNorm_limits hp
      (fun j=>next_ideal_smooth_compact_approx hO hOb (hφ (σ j)) hB hB0 hε k) hscalar hgrad
    · have hnorm (j : ℕ) :
          eLpNorm (fun x=>BMCompactPDE.smoothPositivePart k (φ (σ j) x-B x-ε)-BMCompactPDE.smoothPositivePart k (S x)) q μ≤
            ‖C‖ₑ*eLpNorm (φ (σ j)-u) q μ := by
        rw [←eLpNorm_const_smul]
        apply eLpNorm_mono
        intro x
        have heq : (φ (σ j) x-B x-ε)-S x=φ (σ j) x-u x := by dsimp only [S];ring
        have hb := smoothPositivePart_norm_sub_le k (hbound k) (φ (σ j) x-B x-ε) (S x)
        rw [heq] at hb
        simpa only [Pi.smul_apply,Pi.sub_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC0] using hb
      have hl := ENNReal.Tendsto.const_mul (hLu.comp hσ.tendsto_atTop) (Or.inr (by simp : ‖C‖ₑ≠(∞ : ℝ≥0∞)))
      simp only [mul_zero] at hl
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _=>bot_le) hnorm
    · apply tendsto_eLpNorm_bounded_smul hq0 hqt hq hC0
        (fun j=>(continuous_positivePartSlope k).comp_aestronglyMeasurable (hφS (σ j)).2.1.1)
        ((continuous_positivePartSlope k).comp_aestronglyMeasurable hs.2.1.1)
        (fun j=>(hφS (σ j)).2.2.1) hs.2.2.1
        (fun j x=>hbound k _) (fun x=>hbound k _)
      · filter_upwards [hσlim] with x hx
        exact (continuous_positivePartSlope k).continuousAt.tendsto.comp ((hx.sub_const (B x)).sub_const ε)
      · change Tendsto (fun j=>eLpNorm ((gradient (φ (σ j))-b)-G) q μ) atTop (𝓝 0)
        have heq (j : ℕ) : ((gradient (φ (σ j))-b)-G)=(fun x=>gradient (φ (σ j)) x-g x) := by
          funext x
          dsimp only [G,Pi.sub_apply]
          abel
        simp_rw [heq]
        simpa only [q,μ,Function.comp_def] using hLg.comp hσ.tendsto_atTop

  have hm : AEStronglyMeasurable (fun x=>max (S x) 0) μ :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hs.2.1.1
  have hGm : AEStronglyMeasurable (positivePartGradient S G) μ := by
    change AEStronglyMeasurable ({x | 0<S x}.indicator G) μ
    exact hs.2.2.1.1.indicator₀ (nullMeasurableSet_lt aemeasurable_const hs.2.1.1.aemeasurable)
  have hmLp : MemLp (fun x=>max (S x) 0) q μ := hs.2.1.of_le hm (Eventually.of_forall (fun x=>by
    by_cases hx : S x≤0
    · simp only [max_eq_right hx,norm_zero];exact norm_nonneg _
    · rw [max_eq_left (lt_of_not_ge hx).le]))
  have hGLp : MemLp (positivePartGradient S G) q μ :=
    hs.2.2.1.of_le hGm (Eventually.of_forall (positivePartGradient_norm_le S G))
  apply zeroBoundarySobolevPair_of_eLpNorm_limits hp hSmooth hmLp hGLp
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b:=(2 : ℝ) • S)
    · intro j;exact ((hSmooth j).1.2.1.1).sub hm
    · exact hs.2.1.const_smul (2 : ℝ)
    · intro j
      exact Eventually.of_forall (fun x=>by
        have hn : ‖max (S x) 0‖≤‖S x‖ := by
          by_cases hx : S x≤0
          · simp only [max_eq_right hx,norm_zero];exact norm_nonneg _
          · rw [max_eq_left (lt_of_not_ge hx).le]
        calc
          ‖BMCompactPDE.smoothPositivePart j (S x)-max (S x) 0‖≤‖BMCompactPDE.smoothPositivePart j (S x)‖+‖max (S x) 0‖ := norm_sub_le _ _
          _≤‖S x‖+‖S x‖ := add_le_add (smoothPositivePart_norm_le j _) hn
          _=‖((2 : ℝ) • S) x‖ := by simp [norm_smul];ring)
    · exact Eventually.of_forall (fun x=>tendsto_const_nhds.congr' ((smoothPositivePart_eventually_eq (S x)).mono
        (fun j hj=>by simp only [Pi.sub_apply,hj,sub_self])))
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b:=(C+1) • G)
    · intro j;exact ((hSmooth j).1.2.2.1.1).sub hGm
    · exact hs.2.2.1.const_smul (C+1)
    · intro j
      exact Eventually.of_forall (fun x=>by
        have hn : ‖positivePartGradient S G x‖≤‖G x‖ := positivePartGradient_norm_le S G x
        calc
          ‖positivePartSlope j (S x) • G x-positivePartGradient S G x‖≤‖positivePartSlope j (S x) • G x‖+‖positivePartGradient S G x‖ := norm_sub_le _ _
          _≤C*‖G x‖+‖G x‖ := by
            rw [norm_smul]
            exact add_le_add (mul_le_mul_of_nonneg_right (hbound j _) (norm_nonneg _)) hn
          _=‖((C+1) • G) x‖ := by
            simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤C+1)];ring)
    · exact Eventually.of_forall (fun x=>tendsto_const_nhds.congr' ((positivePartSlope_eventually_eq (S x)).mono
        (fun j hj=>by
          change 0=positivePartSlope j (S x) • G x-positivePartGradient S G x
          rw [hj]
          simp only [positivePartGradient]
          split_ifs <;> simp)))

end BMCompactPDE
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.positivePart_sub_nonnegative_sobolev
