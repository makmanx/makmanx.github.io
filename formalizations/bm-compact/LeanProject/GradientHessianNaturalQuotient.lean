import GradientHessianNaturalMaps

/-! Actual natural-gradient difference quotients inherit the common weighted
weak-PDE bound. The ceiling is independent of epsilon index and quotient length.
No derivative of the natural transform is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem natural_compact_cutoff {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ η : Space n → ℝ,SmoothTest Ω η ∧ (∀ x,0≤η x) ∧ EqOn η 1 K := by
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest Ω η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1⟩
  exact ⟨η,hη,fun x => Real.smoothTransition.nonneg _,fun x hx =>
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)⟩

set_option maxHeartbeats 1200000 in
theorem exists_uniform_local_naturalGradient_quotient_bound_of_uniform_sobolev_data
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)} {ε : ℕ → ℝ}
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    (hu : ∀ j,GlobalWeakRegularizedSourcePair p (ε j) c Ω (u j) (g j))
    (hp : 2≤p) (hε : ∀ j,ε j≠0) (hεb : ∀ j,|ε j|≤1)
    (hΩb : Bornology.IsBounded Ω) {U N : ℝ} (hU : 0≤U) (hN : 0≤N)
    (hNu : ∀ j,(eLpNorm (u j) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤U)
    (hNg : ∀ j,(eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤N)
    (hD : LocalDomain D Ω) :
    ∃ δ B : ℝ,0<δ ∧ 0≤B ∧ ∀ j : ℕ,∀ a : Space n,a≠0 → ‖a‖≤δ →
      MemLp (fun x => ‖a‖⁻¹ • (naturalGradientMap p (ε j) (g j (x+a))-
        naturalGradientMap p (ε j) (g j x))) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (naturalGradientMap p (ε j) (g j (x+a))-
        naturalGradientMap p (ε j) (g j x))‖^2)≤B := by
  let K := closure D
  have hK : IsCompact K := hD.2.1.isCompact_closure
  have hKΩ : K⊆Ω := hD.2.2
  obtain ⟨η,hη,hη0,hη1⟩ := natural_compact_cutoff (hu 0).2.1 hK hKΩ
  obtain ⟨δw,M,hδw,hM,hweighted⟩ :=
    exists_uniform_weighted_gradient_quotient_bound_of_uniform_sobolev_data
      hu hp hε hεb hΩb hU hN hNu hNg hη hη0
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open (hu 0).2.1 hKΩ
  refine ⟨min δw δs,(p/2)^2*M,lt_min hδw hδs,mul_nonneg (sq_nonneg _) hM,?_⟩
  intro j a ha haδ
  have haδw : ‖a‖≤δw := haδ.trans (min_le_left _ _)
  have haδs : ‖a‖≤δs := haδ.trans (min_le_right _ _)
  let O := Ω∩((fun x : Space n => x+a) ⁻¹' Ω)
  let V : Space n → Space n := fun x => naturalGradientMap p (ε j) (g j x)
  let Q : Space n → Space n := fun x => ‖a‖⁻¹ • (g j (x+a)-g j x)
  let T : Space n → Space n := fun x => ‖a‖⁻¹ • (V (x+a)-V x)
  let W : Space n → ℝ := fun x => ((ε j)^2+(max ‖g j (x+a)‖ ‖g j x‖)^2)^((p-2)/2)
  have hDΩ : D⊆Ω := subset_closure.trans hKΩ
  have hDshift : D⊆((fun x : Space n => x+a) ⁻¹' Ω) := by
    intro x hx
    exact hthick (mem_cthickening_of_dist_le (x+a) x δs K (subset_closure hx)
      (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδs))
  have hDO : D⊆O := subset_inter hDΩ hDshift
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hV : MemLp V 2 (volume.restrict Ω) := memLp_naturalGradientMap hp (hu j).2.2.1.2.2.1
  have hVD := hV.mono_measure (Measure.restrict_mono_set volume hDΩ)
  have hVS : MemLp (fun x => V (x+a)) 2 (volume.restrict ((fun x : Space n => x+a) ⁻¹' Ω)) := by
    simpa only [Function.comp_def] using hV.comp_measurePreserving
      (measurePreserving_translation_restrict (hu 0).2.1.measurableSet a)
  have hVSD := hVS.mono_measure (Measure.restrict_mono_set volume hDshift)
  have hT : MemLp T 2 (volume.restrict D) := by
    simpa only [T,Pi.sub_apply,Pi.smul_apply] using! (hVSD.sub hVD).const_smul ‖a‖⁻¹
  refine ⟨hT,?_⟩
  obtain ⟨hIW,hMW⟩ := hweighted j a ha haδw
  have hIW' : Integrable (fun x => η x^2*W x*‖Q x‖^2) (volume.restrict O) := hIW
  have hID := hIW'.mono_measure (Measure.restrict_mono_set volume hDO)
  have hIT : Integrable (fun x => ‖T x‖^2) (volume.restrict D) := hT.integrable_norm_pow (by norm_num)
  have hpoint (x : Space n) : ‖T x‖^2≤(p/2)^2*W x*‖Q x‖^2 := by
    let d : ℝ := ‖a‖⁻¹
    have hd : 0≤d := inv_nonneg.mpr (norm_nonneg _)
    have hscale (v : Space n) : ‖d • v‖^2=d^2*‖v‖^2 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,mul_pow]
    have hh := mul_le_mul_of_nonneg_left
      (naturalGradientMap_difference_sq_le hp (hε j) (g j (x+a)) (g j x)) (sq_nonneg d)
    change ‖d • (naturalGradientMap p (ε j) (g j (x+a))-
      naturalGradientMap p (ε j) (g j x))‖^2≤(p/2)^2*W x*‖d • (g j (x+a)-g j x)‖^2
    rw [hscale,hscale]
    calc
      _≤d^2*((p/2)^2*W x*‖g j (x+a)-g j x‖^2) := hh
      _=_ := by ring
  have hlow : (∫ x in D,‖T x‖^2)≤(p/2)^2*(∫ x in D,η x^2*W x*‖Q x‖^2) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hIT (hID.const_mul ((p/2)^2))
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    have hηx : η x=1 := hη1 (subset_closure hx)
    simpa only [hηx,one_pow,one_mul,mul_assoc] using hpoint x
  have hdom : (∫ x in D,η x^2*W x*‖Q x‖^2)≤∫ x in O,η x^2*W x*‖Q x‖^2 :=
    integral_mono_measure (Measure.restrict_mono_set volume hDO)
      (Eventually.of_forall (fun x => by
        apply mul_nonneg (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _)) (sq_nonneg _))) hIW'
  exact hlow.trans (mul_le_mul_of_nonneg_left (hdom.trans hMW) (sq_nonneg _))

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_local_naturalGradient_quotient_bound_of_uniform_sobolev_data
