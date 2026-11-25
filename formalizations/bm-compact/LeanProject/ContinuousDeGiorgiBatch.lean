import ContinuousWeakCubeBatch
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RegularitySourceBatch

/-! Exact source-body batch: actual relative band measure gain, source normalization,
and radius-uniform actual source-PDE energy. See adjacent provenance. -/

noncomputable section ContinuousBody_ContinuousBandHolder

/-! The actual relative level-band inequality with its De Giorgi measure gain.
The weak field, its Lp membership and all band measurability are derived from
the actual local Sobolev graph. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem continuous_restrict_norm_holder {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ} (hp : 1<p) {g : α → F} (hg : MemLp g (ENNReal.ofReal p) μ)
    (B : Set α) :
    (∫ x in B,‖g x‖ ∂μ) ≤
      (∫ x in B,‖g x‖^p ∂μ)^(1/p)*(μ B).toReal^(1-1/p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := .conjExponent hp
  have hq : 1/Real.conjExponent p=1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall (fun x => norm_nonneg (g x)))
    (Eventually.of_forall (fun _ : α => (by norm_num : (0 : ℝ)≤1)))
    (hg.restrict B).norm
    (memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ))
      (ENNReal.ofReal (Real.conjExponent p)) (μ.restrict B))
  simpa only [mul_one,Real.one_rpow,integral_const,measureReal_def,
    Measure.restrict_apply_univ,smul_eq_mul,mul_one,hq] using hh

theorem SobolevPair.cube_level_band_holder {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hK : IsCompact K) (hcube : continuousUnitCube n⊆K) (hKΩ : K⊆Ω)
    {k l : ℝ} (hkl : k≤l) {Z H : Set (Space n)}
    (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hz : ∀ᵐ x ∂(continuousCubeMeasure n).restrict Z,u x≤k)
    (hh : ∀ᵐ x ∂(continuousCubeMeasure n).restrict H,l≤u x) :
    (l-k)*((continuousCubeMeasure n) Z).toReal*((continuousCubeMeasure n) H).toReal ≤
      (Real.pi/2)*
        (∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂continuousCubeMeasure n)^(1/p)*
        ((continuousCubeMeasure n) {x | k<u x∧u x≤l}).toReal^(1-1/p) := by
  let μ := continuousCubeMeasure n
  have : IsProbabilityMeasure μ := inferInstance
  have hae : ∀ᵐ x ∂μ,x∈Ω :=
    (continuousCubeMeasure_ae_mem n).mono (fun _ hx => hKΩ (hcube hx))
  have hμΩ : μ≤volume.restrict Ω := by
    have hm := Measure.restrict_mono_measure (continuousCubeMeasure_le_volume n) Ω
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm
  have hum : MemLp u (ENNReal.ofReal p) μ := hu.2.1.mono_measure hμΩ
  have hgm : MemLp g (ENNReal.ofReal p) μ := hu.2.2.1.mono_measure hμΩ
  have hB : NullMeasurableSet {x | k<u x∧u x≤l} μ :=
    (nullMeasurableSet_lt aemeasurable_const hum.1.aemeasurable).inter
      (nullMeasurableSet_le hum.1.aemeasurable aemeasurable_const)
  have hb := hu.cube_level_band_poincare hΩ hΩb hK hcube hKΩ hkl hZ hH hz hh
  have he : (∫ x,if k<u x∧u x≤l then ‖g x‖ else 0 ∂μ)=
      ∫ x in {x | k<u x∧u x≤l},‖g x‖ ∂μ := by
    classical
    have hi : (fun x => if k<u x∧u x≤l then ‖g x‖ else 0)=
        {x | k<u x∧u x≤l}.indicator (fun x => ‖g x‖) := by
      funext x
      by_cases hx : k<u x∧u x≤l <;> simp [hx]
    rw [hi]
    exact integral_indicator₀ hB
  rw [he] at hb
  have hs := mul_le_mul_of_nonneg_left
    (continuous_restrict_norm_holder hu.1 hgm {x | k<u x∧u x≤l})
    (show (0 : ℝ)≤Real.pi/2 by positivity)
  exact hb.trans (by simpa only [mul_assoc] using hs)

end BMCompactPDE

end ContinuousBody_ContinuousBandHolder

noncomputable section ContinuousBody_ContinuousSourceNormalize

/-! Actual nonlinear normalization used in the finite-level De Giorgi argument.
The source is multiplied by a^(p-1); it is not silently replaced by zero. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem WeakPSourceSubsolutionPair.affine_positive_actual
    {n : ℕ} {p c a : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (ha : 0<a) (b : ℝ) :
    WeakPSourceSubsolutionPair p (a^(p-1)*c) Ω
      (fun x => a*(u x-b)) (a • g) := by
  have hv := hu.add_const (-b)
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    have hs := (hv.2.2.1 D hD).smul a
    apply hs.congr
    · exact Eventually.of_forall (fun x => by simp only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg])
    · exact Eventually.of_forall (fun _ => rfl)
  · intro D hD θ h hθ hθ0
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ hθ0
    have hscale : fluxPairing p (a • g) h=
        fun x => a^(p-1)*fluxPairing p g h x := by
      funext x
      simp only [fluxPairing,Pi.smul_apply,pFlux_nonneg_smul hu.1 ha.le,real_inner_smul_left]
    rw [hscale]
    refine ⟨hi.const_mul _,?_⟩
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ha.le _)).trans_eq
      (mul_assoc _ _ _).symm

end BMCompactPDE

end ContinuousBody_ContinuousSourceNormalize

noncomputable section ContinuousBody_ContinuousScaleEnergy

/-! Actual source-PDE level energy with the correct radius scaling. No upper
bound or classical regularity is assumed of the input weak representative. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem exists_uniform_source_level_energy (n : ℕ) :
    ∃ G : ℝ,0<G ∧ ∀ {p c : ℝ} {Ω : Set (Space n)}
      {u : Space n → ℝ} {g : Space n → Space n},
      WeakPSourceSubsolutionPair p c Ω u g →
      ∀ (a : Space n) (R : ℝ),0<R → LocalDomain (ball a (3*R)) Ω →
      ∀ (M : ℕ),p≤(M : ℝ) → ∀ k : ℝ,
      (∫ x in ball a R,if k<u x then ‖g x‖^p else 0) ≤
        (M : ℝ)^p*(G/R)^p*(∫ x in ball a (3*R),(max (u x-k) 0)^p)+
          p*|c| *(∫ x in ball a (3*R),max (u x-k) 0) := by
  obtain ⟨G,hG,hcut⟩ := exists_uniform_scaled_cutoff n
  refine ⟨G,hG,?_⟩
  intro p c Ω u g hu a R hR hD M hm k
  obtain ⟨η,hη,hη0,hη1,hηK,_,hgrad⟩ := hcut a R hR
  let D := ball a (3*R)
  let μ := volume.restrict D
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hS := hu.2.2.1 D hD
  have hηM (x : Space n) : η x^M≤1 := pow_le_one₀ (hη0 x) (hη1 x)
  have hGI := integrable_norm_rpow_of_memLp hu.1 hS.2.2.1
  have hs := hS.add (sobolevPair_const hu.1 hD.2.1 (-k))
  have hs' : SobolevPair p D (fun x => u x-k) g :=
    hs.congr (Eventually.of_forall (fun x => by simp only [Pi.add_apply,sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hzm : MemLp (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ := by
    apply hs'.2.1.of_le
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hs'.2.1.1)
    exact Eventually.of_forall (fun x => by
      change ‖max (u x-k) 0‖≤‖u x-k‖
      by_cases hx : u x-k≤0
      · rw [max_eq_right hx,norm_zero]
        exact norm_nonneg _
      · rw [max_eq_left (lt_of_not_ge hx).le])
  have hZI : Integrable (fun x => max (u x-k) 0) μ :=
    MemLp.integrable (ENNReal.one_le_ofReal.mpr hu.1.le) hzm
  have hPI : Integrable (fun x => (max (u x-k) 0)^p) μ := by
    have hi := hzm.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    have he : (fun x => ‖max (u x-k) 0‖^(ENNReal.ofReal p).toReal)=
        (fun x => (max (u x-k) 0)^p) := by
      funext x
      rw [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,
        abs_of_nonneg (le_max_right (u x-k) 0)]
    rwa [he] at hi
  let A : Space n → ℝ := fun x => if k<u x then η x^M*‖g x‖^p else 0
  have hAI : Integrable A μ := by
    have hb : Integrable (fun x => η x^M*‖g x‖^p) μ := by
      apply hGI.mono_nonneg ((hη.1.continuous.pow M).aestronglyMeasurable.mul hGI.1)
      · exact Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (hη0 x) M)
          (Real.rpow_nonneg (norm_nonneg _) _))
      · exact Eventually.of_forall (fun x =>
          (mul_le_mul_of_nonneg_right (hηM x) (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (one_mul _))
    exact hb.indicator₀ (nullMeasurableSet_lt aemeasurable_const hS.2.1.1.aemeasurable)
  have hA0 (x : Space n) : 0≤A x := by
    dsimp only [A]
    split_ifs
    · exact mul_nonneg (pow_nonneg (hη0 x) M) (Real.rpow_nonneg (norm_nonneg _) _)
    · exact le_rfl
  let B : Space n → ℝ := fun x => (max (u x-k) 0)^p*‖gradient η x‖^p
  have hgb (x : Space n) : ‖gradient η x‖^p≤(G/R)^p :=
    Real.rpow_le_rpow (norm_nonneg _) (hgrad x) hp0.le
  have hBmeas : AEStronglyMeasurable B μ := hPI.1.mul
    ((BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1).norm.rpow_const
      (fun _ => Or.inr hp0.le)).aestronglyMeasurable
  have hBpoint (x : Space n) : B x≤(max (u x-k) 0)^p*(G/R)^p :=
    mul_le_mul_of_nonneg_left (hgb x) (Real.rpow_nonneg (le_max_right _ _) _)
  have hBI : Integrable B μ := by
    apply (hPI.mul_const ((G/R)^p)).mono_nonneg hBmeas
    · exact Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall hBpoint
  have hBint : (∫ x,B x ∂μ)≤(G/R)^p*(∫ x,(max (u x-k) 0)^p ∂μ) := by
    have hb := integral_mono_ae hBI (hPI.mul_const ((G/R)^p)) (Eventually.of_forall hBpoint)
    rw [integral_mul_const] at hb
    simpa only [mul_comm] using hb
  let Z : Space n → ℝ := fun x => η x^M*max (u x-k) 0
  have hZpoint (x : Space n) : Z x≤max (u x-k) 0 :=
    (mul_le_mul_of_nonneg_right (hηM x) (le_max_right _ _)).trans_eq (one_mul _)
  have hZ0 (x : Space n) : 0≤Z x := mul_nonneg (pow_nonneg (hη0 x) M) (le_max_right _ _)
  have hZmeas : AEStronglyMeasurable Z μ :=
    (hη.1.continuous.pow M).aestronglyMeasurable.mul hZI.1
  have hZint : Integrable Z μ := hZI.mono_nonneg hZmeas
    (Eventually.of_forall hZ0) (Eventually.of_forall hZpoint)
  have hZle : (∫ x,Z x ∂μ)≤∫ x,max (u x-k) 0 ∂μ :=
    integral_mono_ae hZint hZI (Eventually.of_forall hZpoint)
  have hsource : p*c*(∫ x,Z x ∂μ)≤p*|c| *(∫ x,max (u x-k) 0 ∂μ) := by
    calc
      p*c*(∫ x,Z x ∂μ)≤p*|c| *(∫ x,Z x ∂μ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self c) hp0.le)
          (integral_nonneg hZ0)
      _≤p*|c| *(∫ x,max (u x-k) 0 ∂μ) :=
        mul_le_mul_of_nonneg_left hZle (mul_nonneg hp0.le (abs_nonneg c))
  have hinner : (∫ x in ball a R,if k<u x then ‖g x‖^p else 0)=∫ x in ball a R,A x := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hηx : η x=1 := hηK x (mem_closedBall.mpr (le_of_lt (mem_ball.mp hx)))
    simp only [A,hηx,one_pow,one_mul]
  have hset : ball a R⊆D := ball_subset_ball (by linarith only [hR])
  have hmono : (∫ x in ball a R,A x)≤∫ x in D,A x :=
    setIntegral_mono_set hAI (Eventually.of_forall hA0) (Eventually.of_forall hset)
  have hcacc := hu.caccioppoli_upper_natPow_source hD hη hη0 hη1 hm k
  rw [hinner]
  refine hmono.trans (hcacc.trans ?_)
  have hmul := mul_le_mul_of_nonneg_left hBint (Real.rpow_nonneg (by positivity : 0≤(M : ℝ)) p)
  simpa only [A,B,Z,μ,D,mul_assoc] using add_le_add hmul hsource

end BMCompactPDE

end ContinuousBody_ContinuousScaleEnergy

#print axioms BMCompactPDE.SobolevPair.cube_level_band_holder
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.affine_positive_actual
#print axioms BMCompactPDE.exists_uniform_source_level_energy
