import GradientHessianNaturalSobolev
import GradientHessianNaturalNemytskii
import ExteriorCapacityBridge

/-! Actual unregularized natural-gradient local W1,2 membership, p>=2.
Constructed regularized solutions, uniform natural difference quotients and true
strong-L2 Nemytskii convergence give the quotient bound for the limiting weak
solution. Regional Riesz extraction constructs its weak derivative fields.
No natural-gradient derivative, convergence or desired energy bound is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace BMCompactPDE
private theorem hessian_integral_sq_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal^2=∫ x,f x^2 ∂μ := by
  have he : (∫ x,f x*f x ∂μ)=inner ℝ (hf.toLp f) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [RCLike.inner_apply,hx,starRingEnd_apply,star_trivial]
  simpa only [real_inner_self_eq_norm_sq,Lp.norm_toLp,pow_two] using he.symm

private theorem natural_rows_of_l2_quotients
    {n : ℕ} {Ω D : Set (Space n)} (hΩ : IsOpen Ω) (hD : LocalDomain D Ω)
    {G : Space n → Space n} (hG : MemLp G 2 (volume.restrict Ω))
    (δQ B : ℝ) (hδQ : 0<δQ) (hB : 0≤B)
    (hquot : ∀ a : Space n,a≠0 → ‖a‖≤δQ →
      MemLp (fun x => ‖a‖⁻¹ • (G (x+a)-G x)) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (G (x+a)-G x)‖^2)≤B) :
    ∃ H : Fin n → Space n → Space n,
      (∀ i : Fin n,SobolevPair 2 D (fun x => G x i) (H i)) ∧
      ∀ i k : Fin n,(eLpNorm (fun x => H i x k) 2 (volume.restrict D)).toReal≤Real.sqrt B := by
  classical
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
  let δ := min δQ δs
  have hδ : 0<δ := lt_min hδQ hδs
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  have hcoord : ∀ i j : Fin n,∃ h : Space n → ℝ,
      MemLp h 2 (volume.restrict D) ∧ (eLpNorm h 2 (volume.restrict D)).toReal≤Real.sqrt B ∧
      ∀ φ : Space n → ℝ,SmoothTest D φ →
        Integrable (fun x => G x i*(gradient φ x) j) (volume.restrict D) ∧
        Integrable (fun x => h x*φ x) (volume.restrict D) ∧
        (∫ x in D,G x i*(gradient φ x) j)=-(∫ x in D,h x*φ x) := by
    intro i j
    let F : Space n → ℝ := Ω.indicator (fun x => G x i)
    have hF : MemLp F 2 volume :=
      (memLp_indicator_iff_restrict hΩ.measurableSet).mpr (memLp_coordinate hG i)
    let v : Space n := EuclideanSpace.basisFun (Fin n) ℝ j
    have hv : ‖v‖=1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one j
    have hv0 : v≠0 := norm_ne_zero_iff.mp (by rw [hv];norm_num)
    have hDQevent : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        MemLp (fun x => t⁻¹*(F (x-t • v)-F x)) 2 (volume.restrict D) ∧
        (eLpNorm (fun x => t⁻¹*(F (x-t • v)-F x)) 2 (volume.restrict D)).toReal≤Real.sqrt B := by
      filter_upwards [eventually_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hδ)] with t ht htδ
      have ht0 : t≠0 := ht
      have htδ' : |t|≤δ := (show |t|<δ by
        simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using htδ).le
      let a : Space n := -t • v
      have ha : a≠0 := smul_ne_zero (neg_ne_zero.mpr ht0) hv0
      have hna : ‖a‖=|t| := by simp only [a,norm_smul,Real.norm_eq_abs,abs_neg,hv,mul_one]
      have haδQ : ‖a‖≤δQ := by rw [hna];exact htδ'.trans (min_le_left _ _)
      have haδs : ‖a‖≤δs := by rw [hna];exact htδ'.trans (min_le_right _ _)
      obtain ⟨hQ,hQB⟩ := hquot a ha haδQ
      let Q : Space n → Space n := fun x => ‖a‖⁻¹ • (G (x+a)-G x)
      let q : Space n → ℝ := fun x => t⁻¹*(F (x-t • v)-F x)
      have hqG : MemLp q 2 volume := by
        have hs : MemLp (fun x => F (x-t • v)) 2 volume := by
          simpa only [Function.comp_def,sub_eq_add_neg] using
            hF.comp_measurePreserving (measurePreserving_add_right volume (-(t • v)))
        exact (hs.sub hF).const_mul t⁻¹
      have hq : MemLp q 2 (volume.restrict D) := hqG.restrict D
      refine ⟨hq,?_⟩
      have hqpoint : ∀ᵐ x ∂volume.restrict D,‖q x‖≤‖Q x‖ := by
        filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
        have hxa : x+a∈Ω := hthick (mem_cthickening_of_dist_le (x+a) x δs (closure D)
          (subset_closure hx) (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδs))
        have hxsub : x-t • v=x+a := by simp only [a,neg_smul,sub_eq_add_neg]
        have hqx : q x=t⁻¹*(G (x+a) i-G x i) := by
          simp only [q,hxsub,F,indicator_of_mem hxa,indicator_of_mem (hDΩ hx)]
        rw [hqx,Real.norm_eq_abs,abs_mul,abs_inv]
        have hh := PiLp.norm_apply_le (Q x) i
        simpa only [Q,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,Real.norm_eq_abs,
          abs_mul,abs_inv,abs_norm,hna,abs_abs] using hh
      have hqI : Integrable (fun x => q x^2) (volume.restrict D) := by
        simpa only [Real.norm_eq_abs,sq_abs] using hq.integrable_norm_pow (by norm_num)
      have hQI : Integrable (fun x => ‖Q x‖^2) (volume.restrict D) := hQ.integrable_norm_pow (by norm_num)
      have hsq : (eLpNorm q 2 (volume.restrict D)).toReal^2≤B := by
        rw [hessian_integral_sq_norm hq]
        apply (integral_mono_ae hqI hQI ?_).trans hQB
        filter_upwards [hqpoint] with x hx
        have hh := (sq_le_sq₀ (norm_nonneg (q x)) (norm_nonneg (Q x))).mpr hx
        simpa only [Real.norm_eq_abs,sq_abs] using hh
      exact (Real.le_sqrt ENNReal.toReal_nonneg hB).mpr hsq
    obtain ⟨h,hh,hhN,hhweak⟩ :=
      BMCompactGradientHessian.exists_l2_directional_derivative_of_local_quotient_bound
        hF v (Real.sqrt B) (Real.sqrt_nonneg B) hDQevent
    refine ⟨h,hh,hhN,?_⟩
    intro φ hφ
    have heq : ∀ᵐ x ∂volume.restrict D,F x=G x i := by
      filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
      exact indicator_of_mem (hDΩ hx) _
    obtain ⟨hIf,hIh,hEq⟩ := hhweak φ hφ
    have heqP : (fun x => F x*fderiv ℝ φ x v)=ᵐ[volume.restrict D]
        (fun x => G x i*(gradient φ x) j) := by
      filter_upwards [heq] with x hx
      rw [hx,gradient_coordinate_eq_fderiv]
    refine ⟨hIf.congr heqP,hIh,?_⟩
    rw [←integral_congr_ae heqP]
    exact hEq
  choose h hmem hnorm hweak using hcoord
  let H : Fin n → Space n → Space n := fun i x => WithLp.toLp 2 (fun k => h i k x)
  have hHmem (i : Fin n) : MemLp (H i) 2 (volume.restrict D) := by
    apply memLp_piLp_iff.mpr
    intro k
    change MemLp (fun x => h i k x) 2 (volume.restrict D)
    exact hmem i k
  refine ⟨H,?_,?_⟩
  · intro i
    refine ⟨by norm_num,?_,?_,?_⟩
    · simpa only [ENNReal.ofReal_ofNat] using memLp_coordinate
        (hG.mono_measure (Measure.restrict_mono_set volume hDΩ)) i
    · simpa only [ENNReal.ofReal_ofNat] using hHmem i
    · intro φ hφ k
      exact hweak i k φ hφ
  · intro i k
    exact hnorm i k

private theorem natural_uniform_norm_of_strong_corrections
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {P : ℝ≥0∞} (hP : 1≤P)
    {f : α → F} {w : ℕ → α → F} (hf : MemLp f P μ) (hw : ∀ j,MemLp (w j) P μ)
    (hlim : Tendsto (fun j => eLpNorm (w j) P μ) atTop (𝓝 0)) :
    ∃ N : ℝ,0≤N ∧ ∀ j,(eLpNorm (f+w j) P μ).toReal≤N := by
  have ht : Tendsto (fun j => (eLpNorm (w j) P μ).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠(∞:ℝ≥0∞))).tendsto.comp hlim
  obtain ⟨A,hA,hAb⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  refine ⟨(eLpNorm f P μ).toReal+A,add_nonneg ENNReal.toReal_nonneg hA.le,?_⟩
  intro j
  have hwN : (eLpNorm (w j) P μ).toReal≤A := by
    have hb := hAb ((eLpNorm (w j) P μ).toReal) (mem_range_self j)
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb
  have hs := eLpNorm_add_le hf.1 (hw j).1 hP
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,(hw j).eLpNorm_ne_top⟩) hs
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top (hw j).eLpNorm_ne_top] at hr
  linarith only [hr,hwN]

set_option maxHeartbeats 2400000 in
theorem WeakPSourcePair.exists_local_naturalGradient_sobolev_rows_ge_two
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hp : 2≤p) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ H : Fin n → Space n → Space n,
      ∀ i : Fin n,SobolevPair 2 D (fun x => naturalGradientMap p 0 (gf x) i) (H i) := by
  obtain ⟨w,gw,hw,hu,hg,hwlim⟩ := hH.exists_regularized_source_W1p_approximants hf hn hΩb
  let ε : ℕ → ℝ := fun j => ((j:ℝ)+1)⁻¹
  have hεN (j : ℕ) : ε j≠0 := inv_ne_zero (by positivity : (j:ℝ)+1≠0)
  have hεb (j : ℕ) : |ε j|≤1 := by
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<(j:ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) j])
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have hp1 : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hf.1.le
  obtain ⟨U,hU,hUbound⟩ := natural_uniform_norm_of_strong_corrections hp1 hf.2.1
    (fun j => (hw j).1.2.1) hwlim
  obtain ⟨N,hN,hNbound⟩ := natural_uniform_norm_of_strong_corrections hp1 hf.2.2.1
    (fun j => (hw j).1.2.2.1) hg
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hGconv : Tendsto (fun j => eLpNorm ((gf+gw j)-gf) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0) := by
    have heq (j : ℕ) : (gf+gw j)-gf=gw j := by
      funext x;simp only [Pi.add_apply,Pi.sub_apply,add_sub_cancel_left]
    simpa only [heq] using hg
  have hNem := tendsto_eLpNorm_naturalGradientMap_of_strong_Lp hp
    (fun j => (hu j).2.2.1.2.2.1) hf.2.2.1 hGconv hεN hεb hε
  let V : Space n → Space n := fun x => naturalGradientMap p 0 (gf x)
  let Vj : ℕ → Space n → Space n := fun j x => naturalGradientMap p (ε j) ((gf+gw j) x)
  let S : ℕ → Space n → Space n := fun j x => Vj j x-V x
  have hV : MemLp V 2 (volume.restrict Ω) := memLp_naturalGradientMap hp hf.2.2.1
  have hVj (j : ℕ) : MemLp (Vj j) 2 (volume.restrict Ω) := memLp_naturalGradientMap hp (hu j).2.2.1.2.2.1
  have hS (j : ℕ) : MemLp (S j) 2 (volume.restrict Ω) := (hVj j).sub hV
  have hSconv : Tendsto (fun j => eLpNorm (S j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [S,Vj,V,Pi.sub_apply] using hNem
  obtain ⟨δQ,B,hδQ,hB,hDQ⟩ := exists_uniform_local_naturalGradient_quotient_bound_of_uniform_sobolev_data
    hu hp hεN hεb hΩb hU hN hUbound hNbound hD
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open hH.2.1 hD.2.2
  let δ := min δQ δs
  have hδ : 0<δ := lt_min hδQ hδs
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  have hquot0 : ∀ a : Space n,a≠0 → ‖a‖≤δ →
      MemLp (fun x => ‖a‖⁻¹ • (V (x+a)-V x)) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (V (x+a)-V x)‖^2)≤B := by
    intro a ha haδ
    have haδQ : ‖a‖≤δQ := haδ.trans (min_le_left _ _)
    have haδs : ‖a‖≤δs := haδ.trans (min_le_right _ _)
    have hDshift : D⊆((fun x : Space n => x+a) ⁻¹' Ω) := by
      intro x hx
      exact hthick (mem_cthickening_of_dist_le (x+a) x δs (closure D) (subset_closure hx)
        (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδs))
    let Q0 : Space n → Space n := fun x => ‖a‖⁻¹ • (V (x+a)-V x)
    let Q : ℕ → Space n → Space n := fun j x => ‖a‖⁻¹ • (Vj j (x+a)-Vj j x)
    have hQ (j : ℕ) : MemLp (Q j) 2 (volume.restrict D) := (hDQ j a ha haδQ).1
    have hQB (j : ℕ) : (∫ x in D,‖Q j x‖^2)≤B := (hDQ j a ha haδQ).2
    have hVS : MemLp (fun x => V (x+a)) 2 (volume.restrict ((fun x : Space n => x+a) ⁻¹' Ω)) := by
      simpa only [Function.comp_def] using hV.comp_measurePreserving
        (measurePreserving_translation_restrict hH.2.1.measurableSet a)
    have hQ0 : MemLp Q0 2 (volume.restrict D) := by
      have hs := hVS.mono_measure (Measure.restrict_mono_set volume hDshift)
      have hh := hV.mono_measure (Measure.restrict_mono_set volume hDΩ)
      simpa only [Q0,Pi.sub_apply,Pi.smul_apply] using! (hs.sub hh).const_smul ‖a‖⁻¹
    refine ⟨hQ0,?_⟩
    have hSS (j : ℕ) : MemLp (fun x => S j (x+a)) 2 (volume.restrict D) :=
      ((hS j).comp_measurePreserving
        (measurePreserving_translation_restrict hH.2.1.measurableSet a)).mono_measure
          (Measure.restrict_mono_set volume hDshift)
    have hSD (j : ℕ) : MemLp (S j) 2 (volume.restrict D) :=
      (hS j).mono_measure (Measure.restrict_mono_set volume hDΩ)
    have hlimSS : Tendsto (fun j => eLpNorm (fun x => S j (x+a)) 2 (volume.restrict D)) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSconv (fun _ => bot_le)
      intro j
      have he := eLpNorm_comp_measurePreserving (p:=(2:ℝ≥0∞)) (hS j).1
        (measurePreserving_translation_restrict hH.2.1.measurableSet a)
      exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hDshift)).trans_eq he
    have hlimSD : Tendsto (fun j => eLpNorm (S j) 2 (volume.restrict D)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSconv (fun _ => bot_le)
        (fun j => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hDΩ))
    let R : ℕ → Space n → Space n := fun j x => S j (x+a)-S j x
    have hlimR : Tendsto (fun j => eLpNorm (R j) 2 (volume.restrict D)) atTop (𝓝 0) := by
      have hsum : Tendsto (fun j => eLpNorm (fun x => S j (x+a)) 2 (volume.restrict D)+
          eLpNorm (S j) 2 (volume.restrict D)) atTop (𝓝 0) := by
        simpa only [add_zero] using hlimSS.add hlimSD
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
      intro j
      exact eLpNorm_sub_le (hSS j).1 (hSD j).1 (by norm_num)
    have hQconv : Tendsto (fun j => eLpNorm (Q j-Q0) 2 (volume.restrict D)) atTop (𝓝 0) := by
      have hc : ‖‖a‖⁻¹‖ₑ≠(∞:ℝ≥0∞) := by simp
      have hl := ENNReal.Tendsto.const_mul hlimR (Or.inr hc)
      simp only [mul_zero] at hl
      apply hl.congr'
      exact Eventually.of_forall (fun j => by
        have heq : Q j-Q0=‖a‖⁻¹ • R j := by
          funext x
          simp only [Q,Q0,R,S,Pi.sub_apply,Pi.smul_apply]
          rw [←smul_sub]
          congr 1
          abel
        change ‖‖a‖⁻¹‖ₑ*eLpNorm (R j) 2 (volume.restrict D)=eLpNorm (Q j-Q0) 2 (volume.restrict D)
        rw [heq,eLpNorm_const_smul])
    have hQ2 (j : ℕ) : MemLp (Q j) (ENNReal.ofReal (2:ℝ)) (volume.restrict D) := by
      simpa only [ENNReal.ofReal_ofNat] using! hQ j
    have hQ02 : MemLp Q0 (ENNReal.ofReal (2:ℝ)) (volume.restrict D) := by
      simpa only [ENNReal.ofReal_ofNat] using! hQ0
    have hQconv2 : Tendsto (fun j => eLpNorm (Q j-Q0) (ENNReal.ofReal (2:ℝ))
        (volume.restrict D)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_ofNat] using! hQconv
    have hInt := exterior_integral_energy_tendsto_of_Lp (p:=2) (f:=Q) (g:=Q0)
      (by norm_num : 1<(2:ℝ)) hQ2 hQ02 hQconv2
    have hInt' : Tendsto (fun j => ∫ x in D,‖Q j x‖^2) atTop (𝓝 (∫ x in D,‖Q0 x‖^2)) := by
      simpa only [Real.rpow_two] using hInt
    exact le_of_tendsto hInt' (Eventually.of_forall hQB)
  obtain ⟨H,hrows,-⟩ := natural_rows_of_l2_quotients hH.2.1 hD hV δ B hδ hB hquot0
  exact ⟨H,hrows⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_local_naturalGradient_sobolev_rows_ge_two
