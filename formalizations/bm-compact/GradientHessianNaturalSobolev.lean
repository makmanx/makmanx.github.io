import GradientHessianNaturalQuotient

/-! Constructed regularized natural gradients have actual local W1,2 rows with
function/derivative L2 ceilings independent of epsilon index. No natural-gradient
weak derivative, regularized smoothness or pointwise gradient estimate is input. -/
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

private theorem natural_uniform_l2_norm {n : ℕ} {p : ℝ} (hp : 2≤p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {ε N : ℝ}
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ)
    (hε : |ε|≤1) (hN : 0≤N) (hgN : (eLpNorm g (ENNReal.ofReal p) μ).toReal≤N) :
    (eLpNorm (fun x => naturalGradientMap p ε (g x)) 2 μ).toReal≤
      Real.sqrt (((eLpNorm (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ).toReal+3*N)^p) := by
  let V : Space n → Space n := fun x => naturalGradientMap p ε (g x)
  have hV : MemLp V 2 μ := memLp_naturalGradientMap hp hg
  have he : (eLpNorm V 2 μ).toReal^2=∫ x,‖V x‖^2 ∂μ := by
    simpa only [eLpNorm_norm] using hessian_integral_sq_norm hV.norm
  have hE := regularized_weighted_square_integral_bound (ε:=ε) hp hg hg hg.norm
  have hi : (∫ x,(ε^2+(max ‖g x‖ ‖g x‖)^2)^((p-2)/2)*‖‖g x‖‖^2 ∂μ)=
      ∫ x,‖V x‖^2 ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [V,norm_naturalGradientMap_sq,max_self,Real.norm_eq_abs,abs_norm])
  rw [hi] at hE
  have hA : (eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal≤
      (eLpNorm (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ).toReal := by
    have h1 : MemLp (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ := memLp_const _
    apply ENNReal.toReal_mono h1.eLpNorm_ne_top
    exact eLpNorm_mono_ae (Eventually.of_forall (fun _ => by
      simpa only [Real.norm_eq_abs,abs_abs,abs_one] using hε))
  have hbase : (eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
      (eLpNorm g (ENNReal.ofReal p) μ).toReal+
      (eLpNorm g (ENNReal.ofReal p) μ).toReal+
      (eLpNorm (fun x => ‖g x‖) (ENNReal.ofReal p) μ).toReal≤
      (eLpNorm (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ).toReal+3*N := by
    simp only [eLpNorm_norm]
    linarith only [hA,hgN]
  apply (Real.le_sqrt ENNReal.toReal_nonneg (Real.rpow_nonneg (by positivity) p)).mpr
  rw [he]
  exact hE.trans (Real.rpow_le_rpow (by positivity) hbase (by linarith))

/-- Constructed regularized approximants have actual local W1,2 natural-gradient
components with common function and derivative L2 ceilings, independent of their
positive epsilon index. This does not select C1 representatives of the solutions. -/
theorem WeakPSourcePair.exists_regularized_source_approximants_uniform_natural_sobolev
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hp : 2≤p) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∃ w : ℕ → Space n → ℝ,∃ gw : ℕ → Space n → Space n,
      (∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j)) ∧
      (∀ j : ℕ,GlobalWeakRegularizedSourcePair p (((j:ℝ)+1)⁻¹) c Ω (f+w j) (gf+gw j)) ∧
      Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      (∀ D : Set (Space n),LocalDomain D Ω → ∃ L : ℝ,0≤L ∧ ∀ j : ℕ,
        ∃ H : Fin n → Space n → Space n,
          (∀ i : Fin n,SobolevPair 2 D
            (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹) ((gf+gw j) x) i) (H i)) ∧
          (∀ i : Fin n,(eLpNorm (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹)
            ((gf+gw j) x) i) 2 (volume.restrict D)).toReal≤L) ∧
          ∀ i k : Fin n,(eLpNorm (fun x => H i x k) 2 (volume.restrict D)).toReal≤L) := by
  obtain ⟨w,gw,hw,hu,hg,hwlim⟩ := hH.exists_regularized_source_W1p_approximants hf hn hΩb
  have hp1 : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hf.1.le
  obtain ⟨U,hU,hUbound⟩ := natural_uniform_norm_of_strong_corrections hp1 hf.2.1
    (fun j => (hw j).1.2.1) hwlim
  obtain ⟨N,hN,hNbound⟩ := natural_uniform_norm_of_strong_corrections hp1 hf.2.2.1
    (fun j => (hw j).1.2.2.1) hg
  have hεN (j : ℕ) : ((j:ℝ)+1)⁻¹≠0 := inv_ne_zero (by positivity : (j:ℝ)+1≠0)
  have hεb (j : ℕ) : |((j:ℝ)+1)⁻¹|≤1 := by
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<(j:ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) j])
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let A := Real.sqrt (((eLpNorm (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p)
    (volume.restrict Ω)).toReal+3*N)^p)
  have hA (j : ℕ) : (eLpNorm (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹)
      ((gf+gw j) x)) 2 (volume.restrict Ω)).toReal≤A :=
    natural_uniform_l2_norm hp (hu j).2.2.1.2.2.1 (hεb j) hN (hNbound j)
  refine ⟨w,gw,hw,hu,hg,hwlim,?_⟩
  intro D hD
  obtain ⟨δ,B,hδ,hB,hquot⟩ :=
    exists_uniform_local_naturalGradient_quotient_bound_of_uniform_sobolev_data
      hu hp hεN hεb hΩb hU hN hUbound hNbound hD
  refine ⟨max A (Real.sqrt B),(Real.sqrt_nonneg _).trans (le_max_right _ _),?_⟩
  intro j
  have hV : MemLp (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹) ((gf+gw j) x))
      2 (volume.restrict Ω) := memLp_naturalGradientMap hp (hu j).2.2.1.2.2.1
  obtain ⟨H,hHrows,hHnorm⟩ := natural_rows_of_l2_quotients hH.2.1 hD hV δ B hδ hB (hquot j)
  refine ⟨H,hHrows,?_,?_⟩
  · intro i
    have hbound : eLpNorm (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹) ((gf+gw j) x) i)
        2 (volume.restrict D)≤eLpNorm (fun x => naturalGradientMap p (((j:ℝ)+1)⁻¹)
          ((gf+gw j) x)) 2 (volume.restrict Ω) :=
      (eLpNorm_mono_ae (Eventually.of_forall (fun x => PiLp.norm_apply_le _ i))).trans
        (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (subset_closure.trans hD.2.2)))
    exact ((ENNReal.toReal_mono hV.eLpNorm_ne_top hbound).trans (hA j)).trans (le_max_left _ _)
  · intro i k
    exact (hHnorm i k).trans (le_max_right _ _)

end BMCompactPDE

#print axioms BMCompactPDE.WeakPSourcePair.exists_regularized_source_approximants_uniform_natural_sobolev
