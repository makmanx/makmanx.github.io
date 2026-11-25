import GradientWeightedIntegral

/-! Actual quotient-length-independent local weighted gradient energy for
regularized constant-source weak solutions, p>=2. The scalar quotient ceiling
comes from a constructed compact Sobolev localization. No gradient bound,
weak Hessian, regularity class or desired energy estimate is a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

set_option maxHeartbeats 2400000 in
theorem GlobalWeakRegularizedSourcePair.exists_local_weighted_gradient_quotient_bound_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω)
    {η : Space n → ℝ} (hη : SmoothTest Ω η) (hη0 : ∀ x,0≤η x) :
    ∃ δ M : ℝ,0<δ ∧ 0≤M ∧ ∀ a : Space n,a≠0 → ‖a‖≤δ →
      Integrable (fun x => η x^2*(ε^2+(max ‖g (x+a)‖ ‖g x‖)^2)^((p-2)/2)*
        ‖‖a‖⁻¹ • (g (x+a)-g x)‖^2) (volume.restrict (Ω∩((fun x => x+a) ⁻¹' Ω))) ∧
      (∫ x in Ω∩((fun x => x+a) ⁻¹' Ω),η x^2*
        (ε^2+(max ‖g (x+a)‖ ‖g x‖)^2)^((p-2)/2)*‖‖a‖⁻¹ • (g (x+a)-g x)‖^2)≤M := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  let K := tsupport η
  have hK : IsCompact K := hη.2.1.isCompact
  have hKΩ : K⊆Ω := hη.2.2
  obtain ⟨δg,hδg,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hKΩ
  obtain ⟨δq,Cq,hδq,hCq,hq⟩ := hu.2.2.1.exists_local_difference_quotient_bound hu.2.1 hK hKΩ
  have hgc : Continuous (gradient η) := continuous_gradient_of_contDiff_one (hη.1.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient η x‖≤P := hPb _ (mem_range_self x)
  let μ := volume.restrict K
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hK.isBounded.measure_lt_top.ne
  let A := (eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal
  let N := (eLpNorm g (ENNReal.ofReal p) (volume.restrict Ω)).toReal
  let B := A+2*N+Cq
  let M := 16*(p-1)^2*P^2*B^p
  have hB : 0≤B := by dsimp only [B,A,N];positivity
  refine ⟨min δg δq,M,lt_min hδg hδq,?_,?_⟩
  · dsimp only [M]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      (Real.rpow_nonneg hB _)
  intro a ha haδ
  let d := ‖a‖⁻¹
  let U := Ω∩((fun x : Space n => x+a) ⁻¹' Ω)
  let W : Space n → ℝ := fun x => (ε^2+(max ‖g (x+a)‖ ‖g x‖)^2)^((p-2)/2)
  let z : Space n → ℝ := fun x => d*(u (x+a)-u x)
  let R : Space n → ℝ := fun x => W x*|z x|^2*‖gradient η x‖^2
  have hd : 0≤d := inv_nonneg.mpr (norm_nonneg _)
  have haδg : ‖a‖≤δg := haδ.trans (min_le_left _ _)
  have haδq : ‖a‖≤δq := haδ.trans (min_le_right _ _)
  have hKshift : K⊆((fun x : Space n => x+a) ⁻¹' Ω) := by
    intro x hx
    exact hthick (mem_cthickening_of_dist_le (x+a) x δg K hx
      (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδg))
  have hKU : K⊆U := subset_inter hKΩ hKshift
  have hUo : IsOpen U := hu.2.1.inter (hu.2.1.preimage (continuous_id.add continuous_const))
  have hUb : Bornology.IsBounded U := hΩb.subset inter_subset_left
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  have hηU : SmoothTest U η := ⟨hη.1,hη.2.1,hKU⟩
  have huU := hu.mono_actual inter_subset_left hUo
  have hvU := (hu.translate_actual a).mono_actual inter_subset_right hUo
  have hcc := hvU.caccioppoli_difference_ge_two huU hp hε hUb hηU hη0
  have hgK : MemLp g (ENNReal.ofReal p) μ := hu.2.2.1.2.2.1.mono_measure
    (Measure.restrict_mono_set volume hKΩ)
  have hsu := hu.2.2.1.translate_actual hu.2.1.measurableSet a
  have hsgK : MemLp (fun x => g (x+a)) (ENNReal.ofReal p) μ := hsu.2.2.1.mono_measure
    (Measure.restrict_mono_set volume hKshift)
  have huzK : MemLp u (ENNReal.ofReal p) μ := hu.2.2.1.2.1.mono_measure
    (Measure.restrict_mono_set volume hKΩ)
  have hvzK : MemLp (fun x => u (x+a)) (ENNReal.ofReal p) μ := hsu.2.1.mono_measure
    (Measure.restrict_mono_set volume hKshift)
  have hzK : MemLp z (ENNReal.ofReal p) μ := by
    simpa only [z,Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using! (hvzK.sub huzK).const_smul d
  have hNg : (eLpNorm g (ENNReal.ofReal p) μ).toReal≤N :=
    ENNReal.toReal_mono hu.2.2.1.2.2.1.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hKΩ))
  have hSNorm : eLpNorm (fun x => g (x+a)) (ENNReal.ofReal p)
      (volume.restrict ((fun x => x+a) ⁻¹' Ω))=
      eLpNorm g (ENNReal.ofReal p) (volume.restrict Ω) :=
    eLpNorm_comp_measurePreserving hu.2.2.1.2.2.1.1
      (measurePreserving_translation_restrict hu.2.1.measurableSet a)
  have hNsg : (eLpNorm (fun x => g (x+a)) (ENNReal.ofReal p) μ).toReal≤N := by
    have hh := eLpNorm_mono_measure (p := ENNReal.ofReal p) (fun x => g (x+a))
      (Measure.restrict_mono_set volume hKshift)
    rw [hSNorm] at hh
    exact ENNReal.toReal_mono hu.2.2.1.2.2.1.eLpNorm_ne_top hh
  have hNz : (eLpNorm z (ENNReal.ofReal p) μ).toReal≤Cq := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hq a ha haδq)
    simpa only [z,d,ENNReal.toReal_ofReal hCq] using hh
  have hWI : Integrable (fun x => W x*|z x|^2) μ := by
    simpa only [W,Real.norm_eq_abs] using integrable_regularized_weighted_square
      (ε := ε) hp hsgK hgK hzK
  have hIbound : (∫ x in K,W x*|z x|^2)≤B^p := by
    have hh := regularized_weighted_square_integral_bound (ε := ε) hp hsgK hgK hzK
    have hbase : (eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
        (eLpNorm (fun x => g (x+a)) (ENNReal.ofReal p) μ).toReal+
        (eLpNorm g (ENNReal.ofReal p) μ).toReal+
        (eLpNorm z (ENNReal.ofReal p) μ).toReal≤B := by
      dsimp only [B,A]
      linarith only [hNg,hNsg,hNz]
    have ht := hh.trans (Real.rpow_le_rpow (by positivity) hbase hp0.le)
    simpa only [W,Real.norm_eq_abs,μ] using ht
  have hgradtop : MemLp (gradient η) (∞ : ℝ≥0∞) μ :=
    hgc.memLp_top_of_hasCompactSupport (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1) _
  have hgradpow : MemLp (fun x => ‖gradient η x‖^2) (∞ : ℝ≥0∞) μ := by
    simpa only [pow_two] using hgradtop.norm.mul' hgradtop.norm
  have hRI : Integrable R μ := by
    convert! hWI.mul_of_top_right hgradpow using 1
    funext x
    simp only [R,Pi.mul_apply]
    ring
  have hRbound : (∫ x in K,R x)≤P^2*(∫ x in K,W x*|z x|^2) := by
    have hh := integral_mono hRI (hWI.const_mul (P^2)) (fun x => by
      have hs := (sq_le_sq₀ (norm_nonneg (gradient η x)) hP.le).mpr (hPx x)
      have hWz : 0≤W x*|z x|^2 := mul_nonneg
        (Real.rpow_nonneg (add_nonneg (sq_nonneg ε) (sq_nonneg (max ‖g (x+a)‖ ‖g x‖))) _)
        (sq_nonneg (|z x|))
      have hm := mul_le_mul_of_nonneg_left hs hWz
      simpa only [R,mul_assoc,mul_left_comm,mul_comm] using hm)
    rw [integral_const_mul] at hh
    exact hh
  have hzeroR (x : Space n) (hx : x∉K) : R x=0 := by
    have hh := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hx
    simp [R,hh]
  have hRS (S : Set (Space n)) (hKS : K⊆S) : (∫ x in S,R x)=∫ x,R x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzeroR x (fun hxK => hx (hKS hxK)))
  have hRK : (∫ x in U,R x)=∫ x in K,R x := by rw [hRS U hKU,hRS K Subset.rfl]
  have hgU := huU.2.2.1.2.2.1
  have hvUgrad := hvU.2.2.1.2.2.1
  have hDQ : MemLp (fun x => d • (g (x+a)-g x)) (ENNReal.ofReal p) (volume.restrict U) := by
    simpa only [Pi.sub_apply,Pi.smul_apply,U] using! (hvUgrad.sub hgU).const_smul d
  have hLbase := integrable_regularized_weighted_square (ε := ε) hp hvUgrad hgU hDQ.norm
  have hηtop : MemLp η (∞ : ℝ≥0∞) (volume.restrict U) :=
    hη.1.continuous.memLp_top_of_hasCompactSupport hη.2.1 _
  have hηpow : MemLp (fun x => η x^2) (∞ : ℝ≥0∞) (volume.restrict U) := by
    simpa only [pow_two] using hηtop.mul' hηtop
  have hLQI : Integrable (fun x => η x^2*W x*‖d • (g (x+a)-g x)‖^2) (volume.restrict U) := by
    have hh := hLbase.mul_of_top_right hηpow
    convert! hh using 1
    funext x
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_norm,W]
    ring
  refine ⟨hLQI,?_⟩
  have hLscale : (∫ x in U,η x^2*W x*‖d • (g (x+a)-g x)‖^2)=
      d^2*(∫ x in U,η x^2*W x*‖g (x+a)-g x‖^2) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change η x^2*W x*‖d • (g (x+a)-g x)‖^2=d^2*(η x^2*W x*‖g (x+a)-g x‖^2)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
      ring)
  have hRscale : (∫ x in U,R x)=d^2*
      (∫ x in U,W x*|u (x+a)-u x|^2*‖gradient η x‖^2) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [R,z,abs_mul,pow_two,abs_of_nonneg hd]
      ring)
  change (∫ x in U,η x^2*W x*‖d • (g (x+a)-g x)‖^2)≤M
  calc
    _=d^2*(∫ x in U,η x^2*W x*‖g (x+a)-g x‖^2) := hLscale
    _≤d^2*(16*(p-1)^2*(∫ x in U,W x*|u (x+a)-u x|^2*‖gradient η x‖^2)) :=
      mul_le_mul_of_nonneg_left hcc (sq_nonneg d)
    _=16*(p-1)^2*(∫ x in U,R x) := by rw [hRscale];ring
    _=16*(p-1)^2*(∫ x in K,R x) := by rw [hRK]
    _≤16*(p-1)^2*(P^2*(∫ x in K,W x*|z x|^2)) :=
      mul_le_mul_of_nonneg_left hRbound (by positivity)
    _≤16*(p-1)^2*(P^2*B^p) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hIbound (sq_nonneg P)) (by positivity)
    _=M := by dsimp only [M];ring

end BMCompactPDE
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.exists_local_weighted_gradient_quotient_bound_ge_two
