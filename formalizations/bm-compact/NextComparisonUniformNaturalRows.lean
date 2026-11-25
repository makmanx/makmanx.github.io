import GradientHessianNaturalLimit
import Mathlib.Data.Nat.Pairing

/-! Uniform natural-gradient Sobolev rows for actual weak-solution families.
The member-dependent regularization tails are flattened into ONE sequence
with common original-norm-plus-one ceilings. Genuine uniform natural quotient
bounds then survive each strong-L2 limit. The retained baseline private Riesz
extraction/passage proofs add no public exports; their origins are recorded. -/
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


private theorem next_uniform_natural_rows_of_strong_L2_models
    {n : ℕ} {Ω D : Set (Space n)} (hΩ : IsOpen Ω) (hD : LocalDomain D Ω)
    {V : Space n → Space n} {Vj : ℕ → Space n → Space n}
    (hV : MemLp V 2 (volume.restrict Ω)) (hVj : ∀ j,MemLp (Vj j) 2 (volume.restrict Ω))
    (hConv : Tendsto (fun j=>eLpNorm (Vj j-V) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (δQ B : ℝ) (hδQ : 0<δQ) (hB : 0≤B)
    (hDQ : ∀ j a,a≠0 → ‖a‖≤δQ →
      MemLp (fun x=>‖a‖⁻¹ • (Vj j (x+a)-Vj j x)) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (Vj j (x+a)-Vj j x)‖^2)≤B) :
    ∃ H : Fin n → Space n → Space n,
      (∀ i,SobolevPair 2 D (fun x=>V x i) (H i)) ∧
      ∀ i k,(eLpNorm (fun x=>H i x k) 2 (volume.restrict D)).toReal≤Real.sqrt B := by
  let S : ℕ → Space n → Space n := fun j x=>Vj j x-V x
  have hS (j : ℕ) : MemLp (S j) 2 (volume.restrict Ω) := (hVj j).sub hV
  have hSconv : Tendsto (fun j=>eLpNorm (S j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [S,Pi.sub_apply] using! hConv
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
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
        (measurePreserving_translation_restrict hΩ.measurableSet a)
    have hQ0 : MemLp Q0 2 (volume.restrict D) := by
      have hs := hVS.mono_measure (Measure.restrict_mono_set volume hDshift)
      have hh := hV.mono_measure (Measure.restrict_mono_set volume hDΩ)
      simpa only [Q0,Pi.sub_apply,Pi.smul_apply] using! (hs.sub hh).const_smul ‖a‖⁻¹
    refine ⟨hQ0,?_⟩
    have hSS (j : ℕ) : MemLp (fun x => S j (x+a)) 2 (volume.restrict D) :=
      ((hS j).comp_measurePreserving
        (measurePreserving_translation_restrict hΩ.measurableSet a)).mono_measure
          (Measure.restrict_mono_set volume hDshift)
    have hSD (j : ℕ) : MemLp (S j) 2 (volume.restrict D) :=
      (hS j).mono_measure (Measure.restrict_mono_set volume hDΩ)
    have hlimSS : Tendsto (fun j => eLpNorm (fun x => S j (x+a)) 2 (volume.restrict D)) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSconv (fun _ => bot_le)
      intro j
      have he := eLpNorm_comp_measurePreserving (p:=(2:ℝ≥0∞)) (hS j).1
        (measurePreserving_translation_restrict hΩ.measurableSet a)
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
  exact natural_rows_of_l2_quotients hΩ hD hV δ B hδ hB hquot0

private theorem next_add_Lp_norm_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {q : ℝ≥0∞} (hq : 1≤q)
    {f h : X → E} (hf : MemLp f q μ) (hh : MemLp h q μ)
    {A B : ℝ} (hA : (eLpNorm f q μ).toReal≤A) (hB : (eLpNorm h q μ).toReal≤B) :
    (eLpNorm (f+h) q μ).toReal≤A+B := by
  have hs := eLpNorm_add_le hf.1 hh.1 hq
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,hh.eLpNorm_ne_top⟩) hs
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hh.eLpNorm_ne_top] at ht
  exact ht.trans (add_le_add hA hB)

set_option maxHeartbeats 2400000 in
/-- One natural-gradient weak-derivative ceiling works for every member of
an actual bounded-domain weak-source family with common actual Sobolev norms.
All regularized solutions, approximation tails, natural quotients and weak
derivative fields are constructed. No derivative or desired bound is input. -/
theorem exists_uniform_naturalGradient_sobolev_rows_of_weak_source_family
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    (hH : ∀ j,WeakPSourcePair p c Ω (u j) (g j))
    (hf : ∀ j,SobolevPair p Ω (u j) (g j))
    (hp : 2≤p) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    {U N : ℝ} (hU : 0≤U) (hN : 0≤N)
    (hNu : ∀ j,(eLpNorm (u j) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤U)
    (hNg : ∀ j,(eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤N)
    (hD : LocalDomain D Ω) :
    ∃ M : ℝ,0≤M ∧ ∀ j,∃ H : Fin n → Space n → Space n,
      (∀ i,SobolevPair 2 D (fun x=>naturalGradientMap p 0 (g j x) i) (H i)) ∧
      ∀ i k,(eLpNorm (fun x=>H i x k) 2 (volume.restrict D)).toReal≤M := by
  classical
  choose w gw hw hu hglim hwlim using
    (fun j=>(hH j).exists_regularized_source_W1p_approximants (hf j) hn hΩb)
  have hsmall (j : ℕ) : ∃ J : ℕ,∀ k,J≤k →
      eLpNorm (w j k) (ENNReal.ofReal p) (volume.restrict Ω)<1 ∧
      eLpNorm (gw j k) (ENNReal.ofReal p) (volume.restrict Ω)<1 := by
    exact eventually_atTop.mp (((hwlim j).eventually (eventually_lt_nhds (by norm_num : (0:ℝ≥0∞)<1))).and
      ((hglim j).eventually (eventually_lt_nhds (by norm_num : (0:ℝ≥0∞)<1))))
  choose J hJ using hsmall
  have htail (j k : ℕ) :
      (eLpNorm (w j (k+J j)) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤1 ∧
      (eLpNorm (gw j (k+J j)) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤1 := by
    have hh := hJ j (k+J j) (by omega)
    constructor
    · simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠(∞:ℝ≥0∞)) hh.1.le
    · simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠(∞:ℝ≥0∞)) hh.2.le
  let I : ℕ → ℕ := fun l=>(Nat.unpair l).1
  let K : ℕ → ℕ := fun l=>(Nat.unpair l).2+J (I l)
  let εI : ℕ → ℝ := fun l=>((K l:ℝ)+1)⁻¹
  let uI : ℕ → Space n → ℝ := fun l=>u (I l)+w (I l) (K l)
  let gI : ℕ → Space n → Space n := fun l=>g (I l)+gw (I l) (K l)
  have huI (l : ℕ) : GlobalWeakRegularizedSourcePair p (εI l) c Ω (uI l) (gI l) := hu (I l) (K l)
  have hεI (l : ℕ) : εI l≠0 := inv_ne_zero (by positivity)
  have hεIb (l : ℕ) : |εI l|≤1 := by
    dsimp only [εI]
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<(K l:ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) (K l)])
  have hp1 : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (hf 0).1.le
  have huIb (l : ℕ) : (eLpNorm (uI l) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤U+1 := by
    exact next_add_Lp_norm_bound hp1 (hf (I l)).2.1 (hw (I l) (K l)).1.2.1
      (hNu (I l)) (htail (I l) (Nat.unpair l).2).1
  have hgIb (l : ℕ) : (eLpNorm (gI l) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤N+1 := by
    exact next_add_Lp_norm_bound hp1 (hf (I l)).2.2.1 (hw (I l) (K l)).1.2.2.1
      (hNg (I l)) (htail (I l) (Nat.unpair l).2).2
  obtain ⟨δQ,B,hδQ,hB,hDQ⟩ :=
    exists_uniform_local_naturalGradient_quotient_bound_of_uniform_sobolev_data
      huI hp hεI hεIb hΩb (by linarith only [hU] : 0≤U+1) (by linarith only [hN] : 0≤N+1)
      huIb hgIb hD
  refine ⟨Real.sqrt B,Real.sqrt_nonneg B,?_⟩
  intro j
  let ε : ℕ → ℝ := fun k=>(((k+J j:ℕ):ℝ)+1)⁻¹
  let gj : ℕ → Space n → Space n := fun k=>g j+gw j (k+J j)
  have hgj (k : ℕ) : MemLp (gj k) (ENNReal.ofReal p) (volume.restrict Ω) :=
    (hu j (k+J j)).2.2.1.2.2.1
  have hε (k : ℕ) : ε k≠0 := inv_ne_zero (by positivity)
  have hεb (k : ℕ) : |ε k|≤1 := by
    dsimp only [ε]
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<((k+J j:ℕ):ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) (k+J j)])
  have hεbase : Tendsto (fun k : ℕ=>((k:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have hεlim : Tendsto ε atTop (𝓝 0) := hεbase.comp (tendsto_add_atTop_nat (J j))
  have hGconv : Tendsto (fun k=>eLpNorm (gj k-g j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
    have heq (k : ℕ) : gj k-g j=gw j (k+J j) := by
      funext x
      simp only [gj,Pi.add_apply,Pi.sub_apply,add_sub_cancel_left]
    simpa only [heq,Function.comp_def] using! (hglim j).comp (tendsto_add_atTop_nat (J j))
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hNem := tendsto_eLpNorm_naturalGradientMap_of_strong_Lp hp hgj (hf j).2.2.1 hGconv hε hεb hεlim
  let V : Space n → Space n := fun x=>naturalGradientMap p 0 (g j x)
  let Vj : ℕ → Space n → Space n := fun k x=>naturalGradientMap p (ε k) (gj k x)
  have hV : MemLp V 2 (volume.restrict Ω) := memLp_naturalGradientMap hp (hf j).2.2.1
  have hVj (k : ℕ) : MemLp (Vj k) 2 (volume.restrict Ω) := memLp_naturalGradientMap hp (hgj k)
  have hConv : Tendsto (fun k=>eLpNorm (Vj k-V) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [V,Vj,Pi.sub_apply] using! hNem
  have hDQj (k : ℕ) (a : Space n) (ha : a≠0) (haδ : ‖a‖≤δQ) :
      MemLp (fun x=>‖a‖⁻¹ • (Vj k (x+a)-Vj k x)) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (Vj k (x+a)-Vj k x)‖^2)≤B := by
    simpa only [I,K,εI,gI,Vj,gj,ε,Nat.unpair_pair] using hDQ (Nat.pair j k) a ha haδ
  exact next_uniform_natural_rows_of_strong_L2_models (hH 0).2.1 hD hV hVj hConv δQ B hδQ hB hDQj

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_naturalGradient_sobolev_rows_of_weak_source_family
