import GradientHessianExtraction
import GradientHessianQuotient
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Actual local square-integrable second weak derivatives of fixed-epsilon,
p>=2 regularized weak solutions. No Hessian, differentiability, bounded gradient
or desired quotient estimate is a premise. This is fixed-epsilon H2 only. -/
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

theorem GlobalWeakRegularizedSourcePair.exists_local_l2_weak_hessian_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ C : ℝ,0≤C ∧ ∀ i j : Fin n,∃ h : Space n → ℝ,
      MemLp h 2 (volume.restrict D) ∧ (eLpNorm h 2 (volume.restrict D)).toReal≤C ∧
      ∀ φ : Space n → ℝ,SmoothTest D φ →
        Integrable (fun x => g x i*(gradient φ x) j) (volume.restrict D) ∧
        Integrable (fun x => h x*φ x) (volume.restrict D) ∧
        (∫ x in D,g x i*(gradient φ x) j)=-(∫ x in D,h x*φ x) := by
  obtain ⟨δQ,B,hδQ,hB,hquot⟩ :=
    hu.exists_local_l2_gradient_quotient_bound_ge_two hp hε hΩb hD
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hD.2.2
  let δ := min δQ δs
  have hδ : 0<δ := lt_min hδQ hδs
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have h2p : (2:ℝ≥0∞)≤ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hg2 : MemLp g 2 (volume.restrict Ω) := hu.2.2.1.2.2.1.mono_exponent h2p
  refine ⟨Real.sqrt B,Real.sqrt_nonneg B,?_⟩
  intro i j
  let F : Space n → ℝ := Ω.indicator (fun x => g x i)
  have hF : MemLp F 2 volume :=
    (memLp_indicator_iff_restrict hu.2.1.measurableSet).mpr (memLp_coordinate hg2 i)
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
    let Q : Space n → Space n := fun x => ‖a‖⁻¹ • (g (x+a)-g x)
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
      have hqx : q x=t⁻¹*(g (x+a) i-g x i) := by
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
  have heq : ∀ᵐ x ∂volume.restrict D,F x=g x i := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    exact indicator_of_mem (hDΩ hx) _
  obtain ⟨hIf,hIh,hEq⟩ := hhweak φ hφ
  have heqP : (fun x => F x*fderiv ℝ φ x v)=ᵐ[volume.restrict D]
      (fun x => g x i*(gradient φ x) j) := by
    filter_upwards [heq] with x hx
    rw [hx,gradient_coordinate_eq_fderiv]
  refine ⟨hIf.congr heqP,hIh,?_⟩
  rw [←integral_congr_ae heqP]
  exact hEq

/-- The actual gradient components of a regularized weak solution have genuine
local W1,2 pairs. The rows are constructed from the L2 weak Hessian; no Hessian
field is assumed. -/
theorem GlobalWeakRegularizedSourcePair.exists_local_sobolev_gradient_rows_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ H : Fin n → Space n → Space n,
      ∀ i : Fin n,SobolevPair 2 D (fun x => g x i) (H i) := by
  classical
  obtain ⟨C,hC,hH⟩ := hu.exists_local_l2_weak_hessian_ge_two hp hε hΩb hD
  choose h hmem hnorm hweak using hH
  let H : Fin n → Space n → Space n := fun i x => WithLp.toLp 2 (fun j => h i j x)
  have hHmem (i : Fin n) : MemLp (H i) 2 (volume.restrict D) := by
    apply memLp_piLp_iff.mpr
    intro j
    change MemLp (fun x => h i j x) 2 (volume.restrict D)
    exact hmem i j
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have h2p : (2:ℝ≥0∞)≤ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hg2 : MemLp g 2 (volume.restrict D) :=
    (hu.2.2.1.2.2.1.mono_measure (Measure.restrict_mono_set volume hDΩ)).mono_exponent h2p
  refine ⟨H,?_⟩
  intro i
  refine ⟨by norm_num,?_,?_,?_⟩
  · simpa only [ENNReal.ofReal_ofNat] using memLp_coordinate hg2 i
  · simpa only [ENNReal.ofReal_ofNat] using hHmem i
  · intro φ hφ j
    exact hweak i j φ hφ

end BMCompactPDE
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.exists_local_l2_weak_hessian_ge_two

#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.exists_local_sobolev_gradient_rows_ge_two
