import GradientRegularizedCoercivity
import ExteriorCondenserConstruction

/-! Local full-W0 testing and spatial finite differences for the actually
constructed regularized weak equation. Domain restriction is proved by the
actual zero-extension theorem, not supplied as a property of a PDE class.
These are weak-equation identities, not classical solution regularity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

private def gradientAugmentedProjection (n : ℕ) :
    GradientAugmentedSpace n →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ ℝ (Space n)).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Space n)).toContinuousLinearMap

private theorem gradient_regularized_augmented_norm {n : ℕ} (p ε : ℝ) (v : Space n) :
    ‖(WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n)‖^(p-2)=
      (ε^2+‖v‖^2)^((p-2)/2) := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg ‖v‖))]
  congr 1
  ring

private theorem gradient_memLp_augmented {n : ℕ} {p ε : ℝ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    MemLp (fun x => (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n))
      (ENNReal.ofReal p) μ := by
  have hh := (memLp_const (WithLp.toLp 2 (ε,(0 : Space n)) : GradientAugmentedSpace n)).add
    (hg.continuousLinearMap_comp (gradientAugmentedInjection n))
  convert! hh using 1
  funext x
  simp only [Pi.add_apply]
  rw [gradientAugmentedInjection_apply,←WithLp.toLp_add]
  congr 1
  ext <;> simp

theorem memLp_regularized_pFlux {n : ℕ} {p ε : ℝ} (hp : 1<p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    MemLp (fun x => (ε^2+‖g x‖^2)^((p-2)/2) • g x)
      (ENNReal.ofReal (p/(p-1))) μ := by
  have hG : MemLp (fun x => (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n))
      (ENNReal.ofReal p) μ := gradient_memLp_augmented hg
  have hm : 0<p-1 := sub_pos.mpr hp
  have hN : MemLp (fun x => ‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^(p-1))
      (ENNReal.ofReal (p/(p-1))) μ := by
    simpa only [ENNReal.toReal_ofReal hm.le,←ENNReal.ofReal_div_of_pos hm]
      using hG.norm_rpow_div (ENNReal.ofReal (p-1))
  have hF : MemLp (fun x => pFlux p (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n))
      (ENNReal.ofReal (p/(p-1))) μ := by
    apply (memLp_norm_iff ((continuous_pFlux hp).comp_aestronglyMeasurable hG.1)).mp
    simpa only [norm_pFlux hp] using hN
  have hP := hF.continuousLinearMap_comp (gradientAugmentedProjection n)
  convert! hP using 1
  funext x
  simp only [pFlux,map_smul,gradientAugmentedProjection,ContinuousLinearMap.comp_apply]
  rw [gradient_regularized_augmented_norm]
  rfl

theorem GlobalWeakRegularizedSourcePair.mono_actual {n : ℕ} {p ε c : ℝ}
    {Ω U : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hU : U⊆Ω) (hUo : IsOpen U) :
    GlobalWeakRegularizedSourcePair p ε c U u g := by
  refine ⟨hu.1,hUo,hu.2.2.1.mono_actual hU,?_⟩
  intro θ k hθ
  have hθΩ := hθ.zeroExtend_to_superset hUo.measurableSet hU
  obtain ⟨hi,he⟩ := hu.2.2.2 _ _ hθΩ
  have hflux : (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (U.indicator k x))=
      U.indicator (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x)) := by
    funext x
    by_cases hx : x∈U <;> simp [hx]
  rw [hflux] at hi he
  have hres := hi.mono_measure (Measure.restrict_mono_set volume hU)
  have hI : Integrable (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x))
      (volume.restrict U) := by
    apply hres.congr
    filter_upwards [ae_restrict_mem hUo.measurableSet] with x hx
    exact indicator_of_mem hx _
  rw [setIntegral_indicator hUo.measurableSet,setIntegral_indicator hUo.measurableSet,
    inter_eq_right.mpr hU] at he
  exact ⟨hI,he⟩

theorem GlobalWeakRegularizedSourcePair.translate_actual {n : ℕ} {p ε c : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g) (a : Space n) :
    GlobalWeakRegularizedSourcePair p ε c ((fun x => x+a) ⁻¹' Ω)
      (fun x => u (x+a)) (fun x => g (x+a)) := by
  let S := (fun x : Space n => x+a) ⁻¹' Ω
  have hS : IsOpen S := hu.2.1.preimage (continuous_id.add continuous_const)
  refine ⟨hu.1,hS,hu.2.2.1.translate_actual hu.2.1.measurableSet a,?_⟩
  intro θ k hθ
  have hθΩ : ZeroBoundarySobolevPair p Ω (fun y => θ (y+-a)) (fun y => k (y+-a)) := by
    simpa only [S,preimage_preimage,Function.comp_def,neg_add_cancel_right,preimage_id']
      using hθ.translate_actual hS.measurableSet (-a)
  obtain ⟨hi,he⟩ := hu.2.2.2 _ _ hθΩ
  have ht := measurePreserving_translation_restrict hu.2.1.measurableSet a
  have hemb : MeasurableEmbedding (fun x : Space n => x+a) :=
    (Homeomorph.addRight a).measurableEmbedding
  have hflux : (fun x => inner ℝ ((ε^2+‖g (x+a)‖^2)^((p-2)/2) • g (x+a)) (k x))=
      (fun y => inner ℝ ((ε^2+‖g y‖^2)^((p-2)/2) • g y) (k (y+-a))) ∘
        (fun x => x+a) := by
    funext x
    simp only [Function.comp_apply,add_neg_cancel_right]
  refine ⟨?_,?_⟩
  · rw [hflux]
    exact ht.integrable_comp_of_integrable hi
  · rw [hflux]
    calc
      _ = ∫ y in Ω,inner ℝ ((ε^2+‖g y‖^2)^((p-2)/2) • g y) (k (y+-a)) :=
        ht.integral_comp hemb _
      _ = c*(∫ y in Ω,θ (y+-a)) := he
      _ = c*(∫ x in S,θ x) := by
        congr 1
        have hh := ht.integral_comp hemb (fun y => θ (y+-a))
        simpa only [add_neg_cancel_right] using hh.symm

/-- The actual compact multiplier constructs the full W0 difference test;
common boundary values of the two solutions are not assumed. -/
theorem GlobalWeakRegularizedSourcePair.local_flux_difference_identity
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hv : GlobalWeakRegularizedSourcePair p ε c Ω v h)
    (hΩb : Bornology.IsBounded Ω) {χ : Space n → ℝ} (hχ : SmoothTest Ω χ) :
    Integrable (fun x => χ x*inner ℝ
      ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (g x-h x))
      (volume.restrict Ω) ∧
    Integrable (fun x => (u x-v x)*inner ℝ
      ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (gradient χ x))
      (volume.restrict Ω) ∧
    (∫ x in Ω,χ x*inner ℝ
      ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (g x-h x))=
      -(∫ x in Ω,(u x-v x)*inner ℝ
      ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (gradient χ x)) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have sd : SobolevPair p Ω (u-v) (g-h) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using hu.2.2.1.add (hv.2.2.1.smul (-1))
  let F : Space n → Space n := fun x =>
    (ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x
  let K : Space n → Space n := fun x => χ x • (g x-h x)+(u x-v x) • gradient χ x
  have htest : ZeroBoundarySobolevPair p Ω (fun x => χ x*(u x-v x)) K :=
    sd.mul_smooth_compactSupport_zeroBoundary hu.2.1 hχ.1 hχ.2.1 hχ.2.2
  obtain ⟨hgi,hge⟩ := hu.2.2.2 _ _ htest
  obtain ⟨hhi,hhe⟩ := hv.2.2.2 _ _ htest
  haveI := holderConjugate_p_dual hu.1
  have hF : MemLp F (ENNReal.ofReal (p/(p-1))) (volume.restrict Ω) :=
    (memLp_regularized_pFlux hu.1 hu.2.2.1.2.2.1).sub
      (memLp_regularized_pFlux hv.1 hv.2.2.1.2.2.1)
  have hχtop : MemLp χ (∞ : ℝ≥0∞) (volume.restrict Ω) :=
    hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _
  have hgradtop : MemLp (gradient χ) (∞ : ℝ≥0∞) (volume.restrict Ω) :=
    (continuous_gradient_of_contDiff_one (hχ.1.of_le (by simp))).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1) _
  have hA : Integrable (fun x => χ x*inner ℝ (F x) (g x-h x)) (volume.restrict Ω) := by
    have hx : MemLp (χ • (g-h)) (ENNReal.ofReal p) (volume.restrict Ω) :=
      sd.2.2.1.smul hχtop
    simpa only [Pi.smul_apply',Pi.sub_apply,inner_smul_right] using
      inner_integrable_of_dual_memLp hF hx
  have hB : Integrable (fun x => (u x-v x)*inner ℝ (F x) (gradient χ x))
      (volume.restrict Ω) := by
    have hx : MemLp ((u-v) • gradient χ) (ENNReal.ofReal p) (volume.restrict Ω) :=
      hgradtop.smul sd.2.1
    simpa only [Pi.smul_apply',Pi.sub_apply,inner_smul_right] using
      inner_integrable_of_dual_memLp hF hx
  have hsplit : (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (K x)-
      inner ℝ ((ε^2+‖h x‖^2)^((p-2)/2) • h x) (K x))=
      (fun x => χ x*inner ℝ (F x) (g x-h x))+
      (fun x => (u x-v x)*inner ℝ (F x) (gradient χ x)) := by
    funext x
    simp only [F,K,Pi.add_apply,inner_add_right,inner_smul_right,inner_sub_left]
    ring
  have he : (∫ x in Ω,inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (K x)-
      inner ℝ ((ε^2+‖h x‖^2)^((p-2)/2) • h x) (K x))=0 := by
    rw [integral_sub hgi hhi,hge,hhe,sub_self]
  rw [hsplit] at he
  change (∫ x in Ω,χ x*inner ℝ (F x) (g x-h x)+
    (u x-v x)*inner ℝ (F x) (gradient χ x))=0 at he
  rw [integral_add hA hB] at he
  exact ⟨hA,hB,by linarith only [he]⟩

/-- Actual weighted quadratic difference energy follows from the full weak
equation. The two functions need not agree on the boundary. This is not yet
the quotient-length-independent estimate or a weak-Hessian construction. -/
theorem GlobalWeakRegularizedSourcePair.local_weighted_difference_bound_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hv : GlobalWeakRegularizedSourcePair p ε c Ω v h)
    (hp : 2≤p) (hΩb : Bornology.IsBounded Ω)
    {χ : Space n → ℝ} (hχ : SmoothTest Ω χ) (hχ0 : ∀ x,0≤χ x) :
    Integrable (fun x => χ x*((1/2 : ℝ)*
      (max (Real.sqrt (ε^2+‖g x‖^2)) (Real.sqrt (ε^2+‖h x‖^2)))^(p-2)*‖g x-h x‖^2))
      (volume.restrict Ω) ∧
    (∫ x in Ω,χ x*((1/2 : ℝ)*
      (max (Real.sqrt (ε^2+‖g x‖^2)) (Real.sqrt (ε^2+‖h x‖^2)))^(p-2)*‖g x-h x‖^2))≤
      -(∫ x in Ω,(u x-v x)*inner ℝ
        ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x)
        (gradient χ x)) := by
  obtain ⟨hA,_,he⟩ := hu.local_flux_difference_identity hv hΩb hχ
  have hgm := hu.2.2.1.2.2.1.1
  have hhm := hv.2.2.1.2.2.1.1
  have hweight : AEMeasurable (fun x =>
      (max (Real.sqrt (ε^2+‖g x‖^2)) (Real.sqrt (ε^2+‖h x‖^2)))^(p-2))
      (volume.restrict Ω) :=
    ((aemeasurable_const.add (hgm.norm.aemeasurable.pow_const (2 : ℕ))).sqrt.max
      (aemeasurable_const.add (hhm.norm.aemeasurable.pow_const (2 : ℕ))).sqrt).pow_const _
  have hnorm : AEMeasurable (fun x => ‖g x-h x‖^2) (volume.restrict Ω) :=
    (hgm.sub hhm).norm.aemeasurable.pow_const (2 : ℕ)
  have hm : AEStronglyMeasurable (fun x => χ x*((1/2 : ℝ)*
      (max (Real.sqrt (ε^2+‖g x‖^2)) (Real.sqrt (ε^2+‖h x‖^2)))^(p-2)*‖g x-h x‖^2))
      (volume.restrict Ω) :=
    (hχ.1.continuous.measurable.aemeasurable.mul
      ((hweight.const_mul (1/2 : ℝ)).mul hnorm)).aestronglyMeasurable
  have hpoint (x : Space n) : χ x*((1/2 : ℝ)*
      (max (Real.sqrt (ε^2+‖g x‖^2)) (Real.sqrt (ε^2+‖h x‖^2)))^(p-2)*‖g x-h x‖^2)≤
      χ x*inner ℝ
        ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (g x-h x) :=
    mul_le_mul_of_nonneg_left
      (regularized_pFlux_weighted_monotonicity_ge_two hp ε (g x) (h x)) (hχ0 x)
  have hI := hA.mono' hm (Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by
      exact mul_nonneg (hχ0 x) (mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (le_max_of_le_left (Real.sqrt_nonneg _)) _)) (sq_nonneg _)))]
    exact hpoint x))
  exact ⟨hI,(integral_mono hI hA hpoint).trans_eq he⟩

private theorem gradient_regularized_pairing_augmentation {n : ℕ}
    (p ε : ℝ) (v w : Space n) :
    inner ℝ
      (pFlux p (WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n)-
       pFlux p (WithLp.toLp 2 (ε,w) : GradientAugmentedSpace n))
      ((WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n)-WithLp.toLp 2 (ε,w))=
    inner ℝ ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) (v-w) := by
  have hsub : (WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n)-WithLp.toLp 2 (ε,w)=
      gradientAugmentedInjection n (v-w) := by
    rw [gradientAugmentedInjection_apply,←WithLp.toLp_sub]
    congr 1
    ext <;> simp
  rw [hsub,inner_sub_left,gradientAugmentedFlux_pairing,
    gradientAugmentedFlux_pairing,←inner_sub_left]

/-- Genuine uniqueness of both fields with common full-W0 boundary data.
The conclusion is a.e. equality, as required for raw weak solutions. -/
theorem GlobalWeakRegularizedSourcePair.ae_eq_of_same_source_W0
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hv : GlobalWeakRegularizedSourcePair p ε c Ω v h)
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h)) :
    u =ᵐ[volume.restrict Ω] v ∧ g =ᵐ[volume.restrict Ω] h := by
  obtain ⟨hgi,hge⟩ := hu.2.2.2 _ _ hboundary
  obtain ⟨hhi,hhe⟩ := hv.2.2.2 _ _ hboundary
  let D : Space n → ℝ := fun x => inner ℝ
    ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (g x-h x)
  have hD : D=(fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) ((g-h) x)-
      inner ℝ ((ε^2+‖h x‖^2)^((p-2)/2) • h x) ((g-h) x)) := by
    funext x
    simp only [D,Pi.sub_apply,inner_sub_left]
  have hI : Integrable D (volume.restrict Ω) := by rw [hD];exact hgi.sub hhi
  have he : (∫ x in Ω,D x)=0 := by
    rw [hD,integral_sub hgi hhi,hge,hhe,sub_self]
  have hnonneg : ∀ᵐ x ∂volume.restrict Ω,0≤D x := Eventually.of_forall (fun x => by
    dsimp only [D]
    rw [←gradient_regularized_pairing_augmentation]
    exact pFlux_monotonicity hu.1 _ _)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hI).mp he
  have hgh : g =ᵐ[volume.restrict Ω] h := by
    filter_upwards [hzero] with x hx
    have hpair : inner ℝ
        (pFlux p (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)-
         pFlux p (WithLp.toLp 2 (ε,h x) : GradientAugmentedSpace n))
        ((WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)-WithLp.toLp 2 (ε,h x))=0 := by
      rw [gradient_regularized_pairing_augmentation]
      exact hx
    have haug := (pFlux_pairing_eq_zero_iff hu.1 _ _).mp hpair
    exact congrArg (fun z : GradientAugmentedSpace n => (WithLp.ofLp z).2) haug
  have hgz : g-h =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hgh] with x hx
    simp only [Pi.sub_apply,hx,sub_self,Pi.zero_apply]
  have huz := hboundary.ae_eq_zero_of_gradient_ae_zero hn hu.2.1 hΩb hgz
  refine ⟨?_,hgh⟩
  filter_upwards [huz] with x hx
  exact sub_eq_zero.mp hx

/-- The genuine full weak equation implies the actual augmented p-energy
minimum inequality. No variational-minimum premise is supplied. -/
theorem GlobalWeakRegularizedSourcePair.energy_minimality
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hΩb : Bornology.IsBounded Ω)
    {θ : Space n → ℝ} {k : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ k) :
    (∫ x in Ω,‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p) ≤
      (∫ x in Ω,‖(WithLp.toLp 2 (ε,g x+k x) : GradientAugmentedSpace n)‖^p)-
        p*c*(∫ x in Ω,θ x) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hi : Integrable (fun x => ‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p)
      (volume.restrict Ω) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (gradient_memLp_augmented hu.2.2.1.2.2.1).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hj : Integrable (fun x => ‖(WithLp.toLp 2 (ε,g x+k x) : GradientAugmentedSpace n)‖^p)
      (volume.restrict Ω) := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Pi.add_apply] using
      (gradient_memLp_augmented (hu.2.2.1.2.2.1.add hθ.1.2.2.1)).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  obtain ⟨hI,he⟩ := hu.2.2.2 _ _ hθ
  have hpoint (x : Space n) :
      ‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p+
        p*inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x)≤
      ‖(WithLp.toLp 2 (ε,g x+k x) : GradientAugmentedSpace n)‖^p := by
    have hh := norm_rpow_add_tangent_lower hu.1
      (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n) (gradientAugmentedInjection n (k x))
    rw [gradientAugmentedFlux_pairing,gradientAugmentedInjection_apply,←WithLp.toLp_add] at hh
    simpa only [Prod.mk_add_mk,add_zero] using hh
  have hle := integral_mono (hi.add (hI.const_mul p)) hj hpoint
  change (∫ x in Ω,‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p+
    p*inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x))≤_ at hle
  rw [integral_add hi (hI.const_mul p),integral_const_mul,he] at hle
  linarith only [hle]

theorem GlobalWeakRegularizedSourcePair.harmonic_boundary_energy_bound
    {n : ℕ} {p ε : ℝ} {Ω : Set (Space n)}
    {u f : Space n → ℝ} {g gf : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε 0 Ω u g)
    (hΩb : Bornology.IsBounded Ω)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-f) (g-gf)) :
    (∫ x in Ω,‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p) ≤
      ∫ x in Ω,‖(WithLp.toLp 2 (ε,gf x) : GradientAugmentedSpace n)‖^p := by
  have htest := hboundary.smul_actual (-1)
  have hh := hu.energy_minimality hΩb htest
  simpa only [Pi.smul_apply,Pi.sub_apply,neg_one_smul,neg_sub,
    add_sub_cancel,zero_mul,mul_zero,sub_zero] using hh

/-- A genuine epsilon-independent gradient-energy bound for actual homogeneous
regularized solutions with common Sobolev boundary data, valid for all p>1.
It does not assert pointwise bounds or smoothness of the weak solutions. -/
theorem GlobalWeakRegularizedSourcePair.uniform_harmonic_gradient_energy
    {n : ℕ} {p ε : ℝ} {Ω : Set (Space n)}
    {u f : Space n → ℝ} {g gf : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε 0 Ω u g)
    (hΩb : Bornology.IsBounded Ω) (hf : SobolevPair p Ω f gf)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-f) (g-gf)) (hε : |ε|≤1) :
    (∫ x in Ω,‖g x‖^p)≤∫ x in Ω,(1+‖gf x‖)^p := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hgI := integrable_norm_rpow_of_memLp hu.1 hu.2.2.1.2.2.1
  have hGI : Integrable (fun x => ‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p)
      (volume.restrict Ω) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (gradient_memLp_augmented hu.2.2.1.2.2.1).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hFI : Integrable (fun x => ‖(WithLp.toLp 2 (ε,gf x) : GradientAugmentedSpace n)‖^p)
      (volume.restrict Ω) := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (gradient_memLp_augmented hf.2.2.1).integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hright : Integrable (fun x => (1+‖gf x‖)^p) (volume.restrict Ω) := by
    have hm := (memLp_const (1 : ℝ) : MemLp (fun _ : Space n => (1 : ℝ))
      (ENNReal.ofReal p) (volume.restrict Ω)).add hf.2.2.1.norm
    simpa only [ENNReal.toReal_ofReal hp0.le,Pi.add_apply,Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg zero_le_one (norm_nonneg _))] using
      hm.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  calc
    _≤∫ x in Ω,‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p :=
      integral_mono hgI hGI (fun x => Real.rpow_le_rpow (norm_nonneg _)
        (WithLp.norm_snd_le ℝ (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)) hp0.le)
    _≤∫ x in Ω,‖(WithLp.toLp 2 (ε,gf x) : GradientAugmentedSpace n)‖^p :=
      hu.harmonic_boundary_energy_bound hΩb hboundary
    _≤_ := integral_mono hFI hright (fun x => by
      apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
      have hsplit : (WithLp.toLp 2 (ε,gf x) : GradientAugmentedSpace n)=
          WithLp.toLp 2 (ε,(0 : Space n))+gradientAugmentedInjection n (gf x) := by
        rw [gradientAugmentedInjection_apply,←WithLp.toLp_add]
        congr 1
        ext <;> simp
      rw [hsplit]
      have hzero : ‖(WithLp.toLp 2 (ε,(0 : Space n)) : GradientAugmentedSpace n)‖=|ε| := by
        rw [WithLp.prod_norm_eq_of_L2]
        simp [WithLp.fst,WithLp.snd,Real.sqrt_sq_eq_abs]
      exact (norm_add_le _ _).trans (by rw [hzero,gradientAugmentedInjection_norm];linarith only [hε]))

/-- Construct an actual regularized weak family, with a common epsilon-free
gradient-energy ceiling on |epsilon|<=1. No solution family or uniform energy
estimate is a premise. Classical smoothness and convergence are not claimed. -/
theorem exists_uniform_regularized_harmonic_family
    {n : ℕ} {p : ℝ} (hp : 1<p) (hn : 2≤n) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : Space n → ℝ} {gf : Space n → Space n} (hf : SobolevPair p Ω f gf) :
    ∃ w : ℝ → Space n → ℝ, ∃ gw : ℝ → Space n → Space n,
      ∀ ε : ℝ,ZeroBoundarySobolevPair p Ω (w ε) (gw ε) ∧
        GlobalWeakRegularizedSourcePair p ε 0 Ω (f+w ε) (gf+gw ε) ∧
        (|ε|≤1 → (∫ x in Ω,‖gf x+gw ε x‖^p)≤∫ x in Ω,(1+‖gf x‖)^p) := by
  choose w gw hw hs using (fun ε : ℝ =>
    exists_global_weak_regularized_Dirichlet hp hn hΩ hΩb ε 0 hf)
  refine ⟨w,gw,fun ε => ⟨hw ε,hs ε,?_⟩⟩
  intro hε
  have hboundary : ZeroBoundarySobolevPair p Ω ((f+w ε)-f) ((gf+gw ε)-gf) := by
    apply (hw ε).congr (Eventually.of_forall (fun x => ?_))
      (Eventually.of_forall (fun x => ?_))
    · simp only [Pi.add_apply,Pi.sub_apply,add_sub_cancel_left]
    · simp only [Pi.add_apply,Pi.sub_apply,add_sub_cancel_left]
  exact (hs ε).uniform_harmonic_gradient_energy hΩb hf hboundary hε

end BMCompactPDE
#print axioms BMCompactPDE.memLp_regularized_pFlux
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.mono_actual
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.translate_actual
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.local_flux_difference_identity
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.local_weighted_difference_bound_ge_two
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.ae_eq_of_same_source_W0
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.energy_minimality
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.harmonic_boundary_energy_bound
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.uniform_harmonic_gradient_energy
#print axioms BMCompactPDE.exists_uniform_regularized_harmonic_family
