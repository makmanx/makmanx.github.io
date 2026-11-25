import GradientUniformDifference

/-! Actual unweighted local L2 gradient quotients, derived for fixed nonzero
regularization from the genuine weighted weak-PDE estimate. The epsilon-dependent
constant is constructed; no Hessian or gradient regularity is a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem hessian_compact_cutoff {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ η : Space n → ℝ,SmoothTest Ω η ∧ (∀ x,0≤η x) ∧ EqOn η 1 K := by
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest Ω η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1⟩
  exact ⟨η,hη,fun x => Real.smoothTransition.nonneg _,fun x hx =>
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)⟩

theorem GlobalWeakRegularizedSourcePair.exists_local_l2_gradient_quotient_bound_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ a : Space n,a≠0 → ‖a‖≤δ →
      MemLp (fun x => ‖a‖⁻¹ • (g (x+a)-g x)) 2 (volume.restrict D) ∧
      (∫ x in D,‖‖a‖⁻¹ • (g (x+a)-g x)‖^2)≤C := by
  let K := closure D
  have hK : IsCompact K := hD.2.1.isCompact_closure
  have hKΩ : K⊆Ω := hD.2.2
  obtain ⟨η,hη,hη0,hη1⟩ := hessian_compact_cutoff hu.2.1 hK hKΩ
  obtain ⟨δw,M,hδw,hM,hweighted⟩ :=
    hu.exists_local_weighted_gradient_quotient_bound_ge_two hp hε hΩb hη hη0
  obtain ⟨δs,hδs,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hKΩ
  let L : ℝ := (ε^2)^((p-2)/2)
  have hL : 0<L := Real.rpow_pos_of_pos (sq_pos_of_ne_zero hε) _
  refine ⟨min δw δs,M/L,lt_min hδw hδs,div_nonneg hM hL.le,?_⟩
  intro a ha haδ
  have haδw : ‖a‖≤δw := haδ.trans (min_le_left _ _)
  have haδs : ‖a‖≤δs := haδ.trans (min_le_right _ _)
  let U := Ω∩((fun x : Space n => x+a) ⁻¹' Ω)
  let Q : Space n → Space n := fun x => ‖a‖⁻¹ • (g (x+a)-g x)
  let W : Space n → ℝ := fun x => (ε^2+(max ‖g (x+a)‖ ‖g x‖)^2)^((p-2)/2)
  have hDΩ : D⊆Ω := subset_closure.trans hKΩ
  have hDshift : D⊆((fun x : Space n => x+a) ⁻¹' Ω) := by
    intro x hx
    exact hthick (mem_cthickening_of_dist_le (x+a) x δs K (subset_closure hx)
      (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδs))
  have hDU : D⊆U := subset_inter hDΩ hDshift
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hgD := hu.2.2.1.2.2.1.mono_measure (Measure.restrict_mono_set volume hDΩ)
  have hsg := (hu.2.2.1.translate_actual hu.2.1.measurableSet a).2.2.1.mono_measure
    (Measure.restrict_mono_set volume hDshift)
  have hQp : MemLp Q (ENNReal.ofReal p) (volume.restrict D) := by
    simpa only [Q,Pi.sub_apply,Pi.smul_apply] using! (hsg.sub hgD).const_smul ‖a‖⁻¹
  have h2p : (2:ℝ≥0∞)≤ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hQ : MemLp Q 2 (volume.restrict D) := hQp.mono_exponent h2p
  refine ⟨hQ,?_⟩
  obtain ⟨hIW,hMW⟩ := hweighted a ha haδw
  have hWnonneg (x : Space n) : 0≤W x := Real.rpow_nonneg
    (add_nonneg (sq_nonneg ε) (sq_nonneg _)) _
  have hWlower (x : Space n) : L≤W x := Real.rpow_le_rpow (sq_nonneg ε)
    (le_add_of_nonneg_right (sq_nonneg _)) (by linarith)
  have hIW' : Integrable (fun x => η x^2*W x*‖Q x‖^2) (volume.restrict U) := hIW
  have hID := hIW'.mono_measure (Measure.restrict_mono_set volume hDU)
  have hIQ : Integrable (fun x => ‖Q x‖^2) (volume.restrict D) :=
    hQ.integrable_norm_pow (by norm_num)
  have hlow : L*(∫ x in D,‖Q x‖^2)≤∫ x in D,η x^2*W x*‖Q x‖^2 := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hIQ.const_mul L) hID
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    have hηx : η x=1 := hη1 (subset_closure hx)
    simp only [hηx,one_pow,one_mul]
    exact mul_le_mul_of_nonneg_right (hWlower x) (sq_nonneg _)
  have hdom : (∫ x in D,η x^2*W x*‖Q x‖^2)≤∫ x in U,η x^2*W x*‖Q x‖^2 :=
    integral_mono_measure (Measure.restrict_mono_set volume hDU)
      (Eventually.of_forall (fun x => mul_nonneg (mul_nonneg (sq_nonneg _) (hWnonneg x)) (sq_nonneg _))) hIW'
  have htotal : L*(∫ x in D,‖Q x‖^2)≤M := hlow.trans (hdom.trans hMW)
  apply (le_div_iff₀ hL).mpr
  simpa only [mul_comm] using htotal

end BMCompactPDE
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.exists_local_l2_gradient_quotient_bound_ge_two
