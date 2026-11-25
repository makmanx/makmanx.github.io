import ContinuousCubePoincare
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import RootLpMollification
import RootWeakMollification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import RootSobolevLocalization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.FunProp
import PotentialTruncatedEnergy

/-! Exact source-body batch: cube geometry, genuine weak-graph
approximation, relative L1 Poincare, and uniform cutoffs. See adjacent provenance. -/

noncomputable section ContinuousBody_ContinuousCubeMeasure

/-! The actual uniform cube measure in Euclidean volume coordinates.
No PDE or representative regularity is assumed in these geometric facts. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace BMCompactPDE

def continuousUnitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' Set.univ.pi (fun _ => Ioo (-1 : ℝ) 1)

abbrev continuousCubeMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  OAI.UniformSparsestCut.CubePoincare.cube

theorem continuousUnitCube_measurable (n : ℕ) : MeasurableSet (continuousUnitCube n) := by
  exact (MeasurableSet.univ_pi (fun _ : Fin n => measurableSet_Ioo)).preimage
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurable

private theorem continuous_uniform_pi (n : ℕ) :
    Measure.pi (fun _ : Fin n => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1)) =
      ((2 : ℝ≥0∞)⁻¹)^n • (volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi (fun _ => Ioo (-1 : ℝ) 1)) := by
  have : IsProbabilityMeasure ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1)) := by
    constructor
    norm_num [Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioo]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  haveI : ∀ _ : Fin n,SigmaFinite ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1)) :=
    fun _ => inferInstance
  change Measure.pi (fun _ : Fin n => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1)) =
    ((2 : ℝ≥0∞)⁻¹)^n • (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_pi,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The cube probability law is exactly normalized restricted Euclidean volume. -/
theorem continuousCubeMeasure_eq (n : ℕ) :
    continuousCubeMeasure n = ((2 : ℝ≥0∞)⁻¹)^n •
      (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (continuousUnitCube n) := by
  change (Measure.pi (fun _ : Fin n => (2 : ℝ≥0∞)⁻¹ •
      volume.restrict (Ioo (-1 : ℝ) 1))).map (WithLp.toLp 2) = _
  rw [continuous_uniform_pi,Measure.map_smul]
  congr 1
  change ((volume : Measure (Fin n → ℝ)).restrict
      ((WithLp.toLp 2) ⁻¹' continuousUnitCube n)).map (WithLp.toLp 2) = _
  rw [←Measure.restrict_map (PiLp.volume_preserving_toLp (Fin n)).measurable
    (continuousUnitCube_measurable n),(PiLp.volume_preserving_toLp (Fin n)).map_eq]

/-- In particular, cube-Lp convergence follows from actual whole-space Lp convergence. -/
theorem continuousCubeMeasure_le_volume (n : ℕ) :
    continuousCubeMeasure n ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  rw [continuousCubeMeasure_eq]
  have hc : ((2 : ℝ≥0∞)⁻¹)^n≤1 := pow_le_one₀ bot_le (by norm_num)
  apply Measure.le_iff'.mpr
  intro s
  rw [Measure.smul_apply,smul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    ((one_mul _).trans_le (Measure.restrict_le_self s))

theorem continuousCubeMeasure_ae_mem (n : ℕ) :
    ∀ᵐ x ∂continuousCubeMeasure n, x∈continuousUnitCube n := by
  rw [continuousCubeMeasure_eq]
  exact Measure.ae_smul_measure (ae_restrict_mem (continuousUnitCube_measurable n)) _

def continuousAffineCubeMeasure {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (continuousCubeMeasure n).map (fun x => a+R • x)

instance continuousAffineCubeMeasure_probability {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    IsProbabilityMeasure (continuousAffineCubeMeasure a R) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Every nondegenerate affine cube probability measure has a finite constant
density bound with respect to actual Euclidean volume. -/
theorem continuousAffineCubeMeasure_le_volume {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : R≠0) :
    continuousAffineCubeMeasure a R ≤
      ENNReal.ofReal (abs (R^Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) • volume := by
  have hm := Measure.map_mono (continuousCubeMeasure_le_volume n)
    (show Measurable (fun x : EuclideanSpace ℝ (Fin n) => a+R • x) by fun_prop)
  have hmap : (volume : Measure (EuclideanSpace ℝ (Fin n))).map (fun x => a+R • x) =
      ENNReal.ofReal (abs (R^Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) • volume := by
    rw [show (fun x : EuclideanSpace ℝ (Fin n) => a+R • x)=
      (fun x => a+x)∘(fun x => R • x) from rfl,←Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_addHaar_smul volume hR,Measure.map_smul,map_add_left_eq_self]
  exact hm.trans_eq hmap

end BMCompactPDE

end ContinuousBody_ContinuousCubeMeasure

noncomputable section ContinuousBody_ContinuousWeakApprox

/-! Genuine weak-graph approximation for the cube Poincare transfer.
The smooth sequence and both gradient/value limits are constructed from the
actual distributional graph, not supplied as a regularity hypothesis. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution
namespace BMCompactPDE

private theorem continuous_tendsto_Lp_of_le_smul {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {μ ν : Measure (Space n)} {C q : ℝ≥0∞}
    (hC : C≠(∞ : ℝ≥0∞)) (hμ : μ≤C • ν) (hqt : q≠(∞ : ℝ≥0∞))
    {v : ℕ → Space n → F}
    (hv : Tendsto (fun j => eLpNorm (v j) q ν) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (v j) q μ) atTop (𝓝 0) := by
  have hpow : C^((1/q).toReal)≠(∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hC
  have hlim : Tendsto (fun j => C^((1/q).toReal)*eLpNorm (v j) q ν) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hv (Or.inr hpow)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro j
  exact (eLpNorm_mono_measure _ hμ).trans_eq
    (by simpa only [smul_eq_mul] using eLpNorm_smul_measure_of_ne_top hqt (v j) C)

theorem SobolevPair.exists_smooth_L1_approx_of_measure_le
    {n : ℕ} {p : ℝ} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {C : ℝ≥0∞} (hC : C≠(∞ : ℝ≥0∞))
    (hμ : μ≤C • volume) :
    ∃ φ : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (φ j)) ∧
      (∀ j,Integrable (φ j) μ ∧ Integrable (gradient (φ j)) μ) ∧
      Tendsto (fun j => eLpNorm (φ j-u) 1 μ) atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) 1 μ)
        atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hR (j : ℕ) : 0<R j := by dsimp only [R];positivity
  have hRb (j : ℕ) : R j≤1 := by
    dsimp only [R]
    apply (div_le_iff₀ (by positivity : 0<(j : ℝ)+1)).mpr
    norm_num
  let b : ℕ → ContDiffBump (0 : Space n) := fun j =>
    ⟨R j/2,R j,half_pos (hR j),half_lt_self (hR j)⟩
  have hbl : Tendsto (fun j => (b j).rOut) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [b,R,div_eq_mul_inv,mul_zero,one_mul,Function.comp_apply] using!
      (tendsto_const_nhds (x := (1 : ℝ))).mul (tendsto_inv_atTop_zero.comp hn)
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hu.1.le
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hum : MemLp u q volume := by simpa only [q,Measure.restrict_univ] using hu.2.1
  have hgm : MemLp g q volume := by simpa only [q,Measure.restrict_univ] using hu.2.2.1
  let φ : ℕ → Space n → ℝ := fun j => normalizedMollify (b j) u
  have hφ (j : ℕ) : ContDiff ℝ ∞ (φ j) :=
    ((b j).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (lsmul ℝ ℝ) (b j).contDiff_normed (hum.locallyIntegrable hq)
  have hcomm (j : ℕ) : gradient (φ j)=normalizedMollify (b j) g :=
    hu.gradient_convolution_eq (b j).contDiff_normed (b j).hasCompactSupport_normed
  have hφLp (j : ℕ) : MemLp (φ j) q μ :=
    MemLp.mono_measure hμ ((memLp_normalizedMollify hq hqt (b j) hum).smul_measure hC)
  have hgLp (j : ℕ) : MemLp (gradient (φ j)) q μ := by
    rw [hcomm]
    exact MemLp.mono_measure hμ ((memLp_normalizedMollify hq hqt (b j) hgm).smul_measure hC)
  have huμ : MemLp u q μ := MemLp.mono_measure hμ (hum.smul_measure hC)
  have hgμ : MemLp g q μ := MemLp.mono_measure hμ (hgm.smul_measure hC)
  have hLu := tendsto_eLpNorm_mollify_sub_of_memLp hq hqt hbl
    (by norm_num : (0 : ℝ)≤1) hRb hum
  have hLg := tendsto_eLpNorm_mollify_sub_of_memLp hq hqt hbl
    (by norm_num : (0 : ℝ)≤1) hRb hgm
  have hLuμ : Tendsto (fun j => eLpNorm (φ j-u) q μ) atTop (𝓝 0) := by
    exact continuous_tendsto_Lp_of_le_smul hC hμ hqt hLu
  have hLgμ : Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) q μ)
      atTop (𝓝 0) := by
    simp_rw [hcomm]
    exact continuous_tendsto_Lp_of_le_smul hC hμ hqt hLg
  refine ⟨φ,hφ,fun j => ⟨MemLp.integrable hq (hφLp j),
    MemLp.integrable hq (hgLp j)⟩,?_,?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLuμ
      (fun _ => bot_le)
    intro j
    exact eLpNorm_le_eLpNorm_of_exponent_le hq ((hφLp j).sub huμ).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLgμ
      (fun _ => bot_le)
    intro j
    exact eLpNorm_le_eLpNorm_of_exponent_le hq ((hgLp j).sub hgμ).1

end BMCompactPDE

end ContinuousBody_ContinuousWeakApprox

noncomputable section ContinuousBody_ContinuousWeakPoincare

/-! Actual weak-gradient cube Poincare. Smooth approximation is constructed
from the distributional Sobolev graph; classical regularity is not an input. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

private theorem continuous_norm_integral_limit {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {v : ℕ → α → F}
    (hf : Integrable f μ) (hv : ∀ j,Integrable (v j) μ)
    (hl : Tendsto (fun j => eLpNorm (v j-f) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖v j x‖ ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) := by
  have hb (j : ℕ) : eLpNorm ((fun x => ‖v j x‖)-(fun x => ‖f x‖)) 1 μ ≤
      eLpNorm (v j-f) 1 μ := by
    apply eLpNorm_mono_ae
    exact Eventually.of_forall (fun x => by
      change ‖‖v j x‖-‖f x‖‖≤‖v j x-f x‖
      rw [Real.norm_eq_abs]
      exact abs_norm_sub_norm_le _ _)
  have ht : Tendsto (fun j => eLpNorm ((fun x => ‖v j x‖)-(fun x => ‖f x‖)) 1 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => bot_le) hb
  exact tendsto_integral_of_L1' _ hf.norm.1
    (Eventually.of_forall (fun j => (hv j).norm)) ht

private theorem continuous_pair_integral_limit {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {u : α → ℝ} {φ : ℕ → α → ℝ}
    (hu : Integrable u μ) (hφ : ∀ j,Integrable (φ j) μ)
    (hl : Tendsto (fun j => eLpNorm (φ j-u) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ z : α×α, ‖φ j z.1-φ j z.2‖ ∂μ.prod μ)
      atTop (𝓝 (∫ z : α×α, ‖u z.1-u z.2‖ ∂μ.prod μ)) := by
  let E : ℕ → α → ℝ := fun j => φ j-u
  have hE (j : ℕ) : Integrable (E j) μ := (hφ j).sub hu
  have hpair (f : α → ℝ) (hf : Integrable f μ) :
      Integrable (fun z : α×α => ‖f z.1-f z.2‖) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).norm
  have hb (j : ℕ) :
      eLpNorm ((fun z : α×α => ‖φ j z.1-φ j z.2‖)-
        (fun z : α×α => ‖u z.1-u z.2‖)) 1 (μ.prod μ) ≤
      (2 : ℝ≥0∞)*eLpNorm (E j) 1 μ := by
    have hmono : eLpNorm ((fun z : α×α => ‖φ j z.1-φ j z.2‖)-
        (fun z : α×α => ‖u z.1-u z.2‖)) 1 (μ.prod μ) ≤
        eLpNorm (fun z : α×α => ‖E j z.1‖+‖E j z.2‖) 1 (μ.prod μ) := by
      apply eLpNorm_mono_ae
      exact Eventually.of_forall (fun z => by
        have hn : ‖‖E j z.1‖+‖E j z.2‖‖=‖E j z.1‖+‖E j z.2‖ :=
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
        change ‖‖φ j z.1-φ j z.2‖-‖u z.1-u z.2‖‖≤‖‖E j z.1‖+‖E j z.2‖‖
        rw [hn,Real.norm_eq_abs]
        have hh := abs_norm_sub_norm_le (φ j z.1-φ j z.2) (u z.1-u z.2)
        have he : (φ j z.1-φ j z.2)-(u z.1-u z.2)=E j z.1-E j z.2 := by
          dsimp only [E,Pi.sub_apply]
          ring
        rw [he] at hh
        exact hh.trans (norm_sub_le _ _))
    have hs : eLpNorm (fun z : α×α => ‖E j z.1‖+‖E j z.2‖) 1 (μ.prod μ) ≤
        eLpNorm (fun z : α×α => ‖E j z.1‖) 1 (μ.prod μ)+
          eLpNorm (fun z : α×α => ‖E j z.2‖) 1 (μ.prod μ) :=
      eLpNorm_add_le ((hE j).comp_fst μ).norm.1 ((hE j).comp_snd μ).norm.1 le_rfl
    have hfst : eLpNorm (fun z : α×α => ‖E j z.1‖) 1 (μ.prod μ)=eLpNorm (E j) 1 μ := by
      change eLpNorm ((fun x => ‖E j x‖)∘Prod.fst) 1 (μ.prod μ)=_
      rw [eLpNorm_comp_measurePreserving (hE j).norm.1 measurePreserving_fst,eLpNorm_norm]
    have hsnd : eLpNorm (fun z : α×α => ‖E j z.2‖) 1 (μ.prod μ)=eLpNorm (E j) 1 μ := by
      change eLpNorm ((fun x => ‖E j x‖)∘Prod.snd) 1 (μ.prod μ)=_
      rw [eLpNorm_comp_measurePreserving (hE j).norm.1 measurePreserving_snd,eLpNorm_norm]
    rw [hfst,hsnd] at hs
    simpa only [two_mul] using hmono.trans hs
  have htwo : Tendsto (fun j => (2 : ℝ≥0∞)*eLpNorm (E j) 1 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hl (Or.inr (by norm_num : (2 : ℝ≥0∞)≠(∞ : ℝ≥0∞)))
  have ht : Tendsto (fun j => eLpNorm ((fun z : α×α => ‖φ j z.1-φ j z.2‖)-
      (fun z : α×α => ‖u z.1-u z.2‖)) 1 (μ.prod μ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htwo
      (fun _ => bot_le) hb
  exact tendsto_integral_of_L1' _ (hpair u hu).1
    (Eventually.of_forall (fun j => hpair (φ j) (hφ j))) ht

/-- Genuine cube L1 Poincare for an arbitrary actual distributional Sobolev
pair. The input has no classical derivative or function bound. -/
theorem SobolevPair.cube_pair_poincare {n : ℕ} {p : ℝ}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) :
    (∫ z : Space n×Space n, ‖u z.1-u z.2‖ ∂(continuousCubeMeasure n).prod (continuousCubeMeasure n)) ≤
      (Real.pi/2)*(∫ x, ‖g x‖ ∂continuousCubeMeasure n) := by
  let μ := continuousCubeMeasure n
  haveI : IsProbabilityMeasure μ := inferInstance
  have hμ : μ≤volume := continuousCubeMeasure_le_volume n
  have hq : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hu.1.le
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa using hu.2.1
  have hgm : MemLp g (ENNReal.ofReal p) volume := by simpa using hu.2.2.1
  have huμ : Integrable u μ := MemLp.integrable hq (MemLp.mono_measure hμ hum)
  have hgμ : Integrable g μ := MemLp.integrable hq (MemLp.mono_measure hμ hgm)
  obtain ⟨φ,hφ,hi,hLu,hLg⟩ := hu.exists_smooth_L1_approx_of_measure_le
    (by norm_num : (1 : ℝ≥0∞)≠(∞ : ℝ≥0∞))
    (by simpa only [one_smul] using hμ)
  have hleft := continuous_pair_integral_limit huμ (fun j => (hi j).1) hLu
  have hright := continuous_norm_integral_limit hgμ (fun j => (hi j).2) hLg
  have hineq (j : ℕ) :
      (∫ z : Space n×Space n, ‖φ j z.1-φ j z.2‖ ∂μ.prod μ) ≤
        (Real.pi/2)*(∫ x, ‖gradient (φ j) x‖ ∂μ) := by
    have hh := OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment_oai
      (φ j) ((hφ j).of_le (by simp))
    change (∫ z : Space n×Space n, |φ j z.1-φ j z.2| ∂μ.prod μ) ≤
      (Real.pi/2)*(∫ x, ‖fderiv ℝ (φ j) x‖ ∂μ) at hh
    have hn (x : Space n) : ‖fderiv ℝ (φ j) x‖=‖gradient (φ j) x‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map]
    simpa only [Real.norm_eq_abs,hn] using hh
  exact le_of_tendsto_of_tendsto hleft (tendsto_const_nhds.mul hright)
    (Eventually.of_forall hineq)

/-- An actual relative L1 Poincare estimate from a measurable zero set.
The positive fraction used later in De Giorgi is geometric data, not a
regularity/oscillation hypothesis. -/
theorem SobolevPair.cube_zero_set_poincare {n : ℕ} {p : ℝ}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) {Z : Set (Space n)} (hZ : MeasurableSet Z)
    (hz : ∀ᵐ x ∂(continuousCubeMeasure n).restrict Z,u x=0) :
    ((continuousCubeMeasure n) Z).toReal*(∫ x,‖u x‖ ∂continuousCubeMeasure n) ≤
      (Real.pi/2)*(∫ x,‖g x‖ ∂continuousCubeMeasure n) := by
  classical
  let μ := continuousCubeMeasure n
  haveI : IsProbabilityMeasure μ := inferInstance
  have hq : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hu.1.le
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa using hu.2.1
  have huμ : Integrable u μ := MemLp.integrable hq
    (MemLp.mono_measure (continuousCubeMeasure_le_volume n) hum)
  let F : Space n×Space n → ℝ := fun z => if z.2∈Z then ‖u z.1‖ else 0
  have hFI : Integrable F (μ.prod μ) :=
    (huμ.norm.comp_fst μ).indicator (hZ.preimage measurable_snd)
  have hpairI : Integrable (fun z : Space n×Space n => ‖u z.1-u z.2‖) (μ.prod μ) :=
    ((huμ.comp_fst μ).sub (huμ.comp_snd μ)).norm
  have hzero : ∀ᵐ y ∂μ,y∈Z → u y=0 := (ae_restrict_iff' hZ).mp hz
  have hpoint : F≤ᵐ[μ.prod μ] fun z => ‖u z.1-u z.2‖ := by
    filter_upwards [(measurePreserving_snd (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hzero]
      with z hz
    by_cases hy : z.2∈Z
    · simp only [F,if_pos hy,hz hy,sub_zero,le_refl]
    · simp only [F,if_neg hy]
      exact norm_nonneg _
  have hbound := integral_mono_ae hFI hpairI hpoint
  have hFint : (∫ z,F z ∂μ.prod μ)=(μ Z).toReal*(∫ x,‖u x‖ ∂μ) := by
    rw [integral_prod _ hFI]
    change (∫ x,(∫ y,Z.indicator (fun _ : Space n => ‖u x‖) y ∂μ) ∂μ)=_
    simp_rw [integral_indicator hZ]
    simp only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
    rw [integral_const_mul]
  rw [hFint] at hbound
  exact hbound.trans hu.cube_pair_poincare

/-- The same estimate is local: a genuine compact smooth localization is
constructed, so whole-space Sobolev membership is not required of the input. -/
theorem SobolevPair.cube_pair_poincare_local {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hcube : continuousUnitCube n⊆K) (hKΩ : K⊆Ω) :
    (∫ z : Space n×Space n,‖u z.1-u z.2‖
      ∂(continuousCubeMeasure n).prod (continuousCubeMeasure n)) ≤
      (Real.pi/2)*(∫ x,‖g x‖ ∂continuousCubeMeasure n) := by
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hχs : tsupport χ⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) f).trans hf.2.2.1
  have hχc : HasCompactSupport χ :=
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos le_rfl)
  have hχ1 (x : Space n) (hx : x∈K) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hχg (x : Space n) (hx : x∈K) : gradient χ x=0 := by
    have hm : IsLocalMax χ x := Eventually.of_forall (fun y => by
      rw [hχ1 x hx]
      exact Real.smoothTransition.le_one (f y))
    unfold gradient
    rw [hm.fderiv_eq_zero]
    exact map_zero _
  have hglobal := hu.mul_smooth_compactSupport_global hΩ hχ hχc hχs
  have hh := hglobal.cube_pair_poincare
  let μ := continuousCubeMeasure n
  haveI : IsProbabilityMeasure μ := inferInstance
  have hv : (fun x => χ x*u x)=ᵐ[μ]u := by
    filter_upwards [continuousCubeMeasure_ae_mem n] with x hx
    simp only [hχ1 x (hcube hx),one_mul]
  have hg : (fun x => χ x • g x+u x • gradient χ x)=ᵐ[μ]g := by
    filter_upwards [continuousCubeMeasure_ae_mem n] with x hx
    simp only [hχ1 x (hcube hx),hχg x (hcube hx),one_smul,smul_zero,add_zero]
  have hp : (fun z : Space n×Space n => ‖χ z.1*u z.1-χ z.2*u z.2‖)=ᵐ[μ.prod μ]
      (fun z => ‖u z.1-u z.2‖) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hv,
      measurePreserving_snd.quasiMeasurePreserving.ae hv] with z h1 h2
    rw [h1,h2]
  have hgn : (fun x => ‖χ x • g x+u x • gradient χ x‖)=ᵐ[μ](fun x => ‖g x‖) :=
    hg.fun_comp norm
  rw [integral_congr_ae hp,integral_congr_ae hgn] at hh
  exact hh

private theorem continuous_smooth_affine_cube_poincare {n : ℕ}
    (a : Space n) {R : ℝ} (hR : 0<R) (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f) :
    (∫ z : Space n×Space n,‖f z.1-f z.2‖
      ∂(continuousAffineCubeMeasure a R).prod (continuousAffineCubeMeasure a R)) ≤
      ((Real.pi/2)*R)*(∫ x,‖gradient f x‖ ∂continuousAffineCubeMeasure a R) := by
  let T : Space n → Space n := fun x => a+R • x
  have hT : Measurable T := by dsimp only [T];fun_prop
  have hfc : ContDiff ℝ 1 (f∘T) := hf.comp (by dsimp only [T];fun_prop)
  have hh := OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment_oai (f∘T) hfc
  change (∫ z : Space n×Space n,|(f∘T) z.1-(f∘T) z.2|
    ∂(continuousCubeMeasure n).prod (continuousCubeMeasure n)) ≤
      (Real.pi/2)*(∫ x,‖fderiv ℝ (f∘T) x‖ ∂continuousCubeMeasure n) at hh
  have hn (x : Space n) : ‖fderiv ℝ (f∘T) x‖=R*‖gradient f (T x)‖ := by
    have hd := fderiv_comp_smul (𝕜:=ℝ) (f:=fun z : Space n => f (a+z)) (x:=x) R
    rw [fderiv_comp_add_left] at hd
    change fderiv ℝ (f∘T) x=R • fderiv ℝ f (T x) at hd
    rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    simp only [gradient,LinearIsometryEquiv.norm_map]
  simp_rw [hn] at hh
  rw [integral_const_mul] at hh
  change (∫ z : Space n×Space n,‖f z.1-f z.2‖
    ∂((continuousCubeMeasure n).map T).prod ((continuousCubeMeasure n).map T)) ≤
      ((Real.pi/2)*R)*(∫ x,‖gradient f x‖ ∂(continuousCubeMeasure n).map T)
  rw [Measure.map_prod_map _ _ hT hT,integral_map (hT.prodMap hT).aemeasurable]
  · rw [integral_map hT.aemeasurable]
    · simpa only [Function.comp_apply,Prod.map_fst,Prod.map_snd,Real.norm_eq_abs,mul_assoc]
        using hh
    · exact (BMCompactPDE.continuous_gradient_of_contDiff_one hf).norm.aestronglyMeasurable
  · exact ((hf.continuous.comp continuous_fst).sub
      (hf.continuous.comp continuous_snd)).norm.aestronglyMeasurable

/-- The actual weak-gradient estimate has the correct linear radius factor on
every nondegenerate translated/dilated cube. Smooth approximants are derived
from the actual graph; the estimate is not a supplied regularity premise. -/
theorem SobolevPair.affine_cube_pair_poincare {n : ℕ} {p : ℝ}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) (a : Space n) {R : ℝ} (hR : 0<R) :
    (∫ z : Space n×Space n,‖u z.1-u z.2‖
      ∂(continuousAffineCubeMeasure a R).prod (continuousAffineCubeMeasure a R)) ≤
      ((Real.pi/2)*R)*(∫ x,‖g x‖ ∂continuousAffineCubeMeasure a R) := by
  let μ := continuousAffineCubeMeasure a R
  let C : ℝ≥0∞ := ENNReal.ofReal (abs (R^Module.finrank ℝ (Space n))⁻¹)
  have hC : C≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hμ : μ≤C • volume := continuousAffineCubeMeasure_le_volume a hR.ne'
  have hq : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hu.1.le
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa using hu.2.1
  have hgm : MemLp g (ENNReal.ofReal p) volume := by simpa using hu.2.2.1
  have huμ : Integrable u μ := MemLp.integrable hq (MemLp.mono_measure hμ (hum.smul_measure hC))
  have hgμ : Integrable g μ := MemLp.integrable hq (MemLp.mono_measure hμ (hgm.smul_measure hC))
  obtain ⟨φ,hφ,hi,hLu,hLg⟩ := hu.exists_smooth_L1_approx_of_measure_le hC hμ
  have hleft := continuous_pair_integral_limit huμ (fun j => (hi j).1) hLu
  have hright := continuous_norm_integral_limit hgμ (fun j => (hi j).2) hLg
  exact le_of_tendsto_of_tendsto hleft (tendsto_const_nhds.mul hright)
    (Eventually.of_forall (fun j => continuous_smooth_affine_cube_poincare a hR (φ j)
      ((hφ j).of_le (by simp))))

end BMCompactPDE

end ContinuousBody_ContinuousWeakPoincare

noncomputable section ContinuousBody_ContinuousScaledCutoff

/-! Radius-uniform smooth cutoffs.  The bound is a fixed dimensional constant
divided by the radius, rather than an unspecified new bound for every ball. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem exists_uniform_scaled_cutoff (n : ℕ) :
    ∃ G : ℝ, 0<G ∧ ∀ (a : Space n) (R : ℝ), 0<R →
      ∃ η : Space n → ℝ,
        SmoothTest (ball a (3*R)) η ∧
        (∀ x,0≤η x) ∧ (∀ x,η x≤1) ∧
        (∀ x∈closedBall a R,η x=1) ∧
        tsupport η⊆closedBall a (2*R) ∧
        ∀ x,‖gradient η x‖≤G/R := by
  let β : ContDiffBump (0 : Space n) := ⟨1,2,by norm_num,by norm_num⟩
  have hβ : ContDiff ℝ ∞ (β : Space n → ℝ) := β.contDiff
  have hβg : Continuous (gradient (β : Space n → ℝ)) :=
    BMCompactCapacityV2.continuous_gradient_of_contDiff hβ
  obtain ⟨C,hC⟩ :=
    (BMCompactCapacityV2.gradient_hasCompactSupport β.hasCompactSupport).exists_bound_of_continuous hβg
  let G : ℝ := max C 1
  have hG : 0<G := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
  have hGb (x : Space n) : ‖gradient (β : Space n → ℝ) x‖≤G :=
    (hC x).trans (le_max_left C 1)
  refine ⟨G,hG,?_⟩
  intro a R hR
  let η : Space n → ℝ := fun x => β (R⁻¹ • (x-a))
  have hη : ContDiff ℝ ∞ η := by dsimp only [η];fun_prop
  have hts : tsupport η⊆closedBall a (2*R) := by
    have ht := tsupport_comp_subset_preimage (β : Space n → ℝ)
      (show Continuous (fun x : Space n => R⁻¹ • (x-a)) by fun_prop)
    intro x hx
    have hxβ := ht hx
    rw [β.tsupport_eq] at hxβ
    have hn : R⁻¹*‖x-a‖≤2 := by
      simpa only [β,mem_preimage,mem_closedBall_iff_norm,sub_zero,norm_smul,
        Real.norm_eq_abs,abs_inv,abs_of_pos hR] using hxβ
    change ‖x-a‖≤2*R
    calc
      ‖x-a‖=R*(R⁻¹*‖x-a‖) := by
        rw [←mul_assoc,mul_inv_cancel₀ hR.ne',one_mul]
      _≤R*2 := mul_le_mul_of_nonneg_left hn hR.le
      _=2*R := mul_comm _ _
  have hc : HasCompactSupport η :=
    (isCompact_closedBall a (2*R)).of_isClosed_subset (isClosed_tsupport η) hts
  have hs : tsupport η⊆ball a (3*R) := by
    intro x hx
    have hh : dist x a≤2*R := hts hx
    exact lt_of_le_of_lt hh (by linarith only [hR])
  refine ⟨η,⟨hη,hc,hs⟩,(fun x => β.nonneg),(fun x => β.le_one),?_,hts,?_⟩
  · intro x hx
    apply β.one_of_mem_closedBall
    rw [mem_closedBall_iff_norm,sub_zero]
    change ‖R⁻¹ • (x-a)‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hn : ‖x-a‖≤R := hx
    calc
      R⁻¹*‖x-a‖≤R⁻¹*R := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hR.le)
      _=1 := inv_mul_cancel₀ hR.ne'
  · intro x
    have hgn (f : Space n → ℝ) (y : Space n) :
        ‖gradient f y‖=‖fderiv ℝ f y‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map]
    rw [hgn]
    change ‖fderiv ℝ (fun y : Space n => β (R⁻¹ • (y-a))) x‖≤G/R
    have hd := fderiv_comp_sub (𝕜:=ℝ) (f:=fun y : Space n => β (R⁻¹ • y)) (x:=x) a
    have hds := fderiv_comp_smul (𝕜:=ℝ) (f:=(β : Space n → ℝ)) (x:=x-a) R⁻¹
    have hder := hd.trans hds
    rw [hder,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_of_pos hR,←hgn]
    calc
      R⁻¹*‖gradient (β : Space n → ℝ) (R⁻¹ • (x-a))‖≤R⁻¹*G :=
        mul_le_mul_of_nonneg_left (hGb _) (inv_nonneg.mpr hR.le)
      _=G/R := by ring

end BMCompactPDE

end ContinuousBody_ContinuousScaledCutoff

noncomputable section ContinuousBody_ContinuousBand

/-! Actual distributional truncation bands and relative level-set separation.
The band field is derived from two genuine full-W0 positive-part tests. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

private theorem continuous_tsupport_of_zero_outside {n : ℕ} {F : Type*} [Zero F]
    {χ : Space n → ℝ} {v : Space n → F}
    (hv : ∀ x,x∉tsupport χ → v x=0) : tsupport v⊆tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  exact hx (hv x hn)

/-- A relative L1 estimate for two separated level sets of an arbitrary actual
Sobolev pair. Only the weak gradient on the intervening half-open band appears.
No continuity, derivative, input bound, or unexplained oscillation estimate is
assumed of the weak representative. -/
theorem SobolevPair.cube_level_band_poincare {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hK : IsCompact K) (hcube : continuousUnitCube n⊆K) (hKΩ : K⊆Ω)
    {k l : ℝ} (hkl : k≤l) {Z H : Set (Space n)}
    (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hz : ∀ᵐ x ∂(continuousCubeMeasure n).restrict Z,u x≤k)
    (hh : ∀ᵐ x ∂(continuousCubeMeasure n).restrict H,l≤u x) :
    (l-k)*((continuousCubeMeasure n) Z).toReal*((continuousCubeMeasure n) H).toReal ≤
      (Real.pi/2)*(∫ x,if k<u x∧u x≤l then ‖g x‖ else 0 ∂continuousCubeMeasure n) := by
  classical
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : ContDiff ℝ ∞ η := Real.smoothTransition.contDiff.comp hf.1
  have hηc : HasCompactSupport η :=
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos le_rfl)
  have hηs : tsupport η⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) f).trans hf.2.2.1
  have hη0 (x : Space n) : 0≤η x := Real.smoothTransition.nonneg (f x)
  have hη1 (x : Space n) : η x≤1 := Real.smoothTransition.le_one (f x)
  have hηK (x : Space n) (hx : x∈K) : η x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hηg (x : Space n) (hx : x∈K) : gradient η x=0 := by
    have hm : IsLocalMax η x := Eventually.of_forall (fun y => by rw [hηK x hx];exact hη1 y)
    unfold gradient
    rw [hm.fderiv_eq_zero]
    exact map_zero _
  let V : ℝ → Space n → ℝ := fun t x => η x^2*max (u x-t) 0
  let G : ℝ → Space n → Space n := fun t x => if t<u x then
    η x^2 • g x+((2 : ℝ)*η x*(u x-t)) • gradient η x else 0
  have hVG (t : ℝ) : SobolevPair p univ (V t) (G t) := by
    have hw := hu.upperCutoff_zeroBoundary hΩ hΩb ⟨hη,hηc,hηs⟩ hη0 (by norm_num : 2≤2) t
    have hw' : ZeroBoundarySobolevPair p Ω (V t) (G t) := by
      simpa only [V,G,Nat.cast_ofNat,Nat.reduceSub,pow_one] using hw
    have hv : tsupport (V t)⊆tsupport η := by
      apply continuous_tsupport_of_zero_outside
      intro x hx
      simp only [V,image_eq_zero_of_notMem_tsupport hx,zero_pow (by decide : 2≠0),zero_mul]
    have hg : tsupport (G t)⊆tsupport η := by
      apply continuous_tsupport_of_zero_outside
      intro x hx
      have hηz := image_eq_zero_of_notMem_tsupport hx
      have hgz := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hx
      simp [G,hηz,hgz]
    exact hw'.1.global_of_compact_support hΩ hηc.isCompact hv hg hηs
  let v : Space n → ℝ := fun x => V k x-V l x
  let b : Space n → Space n := fun x => G k x-G l x
  have hvb : SobolevPair p univ v b := by
    have hb := (hVG k).add ((hVG l).smul (-1))
    apply hb.congr
    · exact Eventually.of_forall (fun x => by simp [v,sub_eq_add_neg,Pi.add_apply,Pi.smul_apply])
    · exact Eventually.of_forall (fun x => by simp [b,sub_eq_add_neg,Pi.add_apply,Pi.smul_apply])
  let μ := continuousCubeMeasure n
  haveI : IsProbabilityMeasure μ := inferInstance
  have hvμ : Integrable v μ := MemLp.integrable
    (ENNReal.one_le_ofReal.mpr hu.1.le)
    (MemLp.mono_measure (continuousCubeMeasure_le_volume n)
      (by simpa only [Measure.restrict_univ] using hvb.2.1))
  have hveq : ∀ᵐ x ∂μ,v x=max (u x-k) 0-max (u x-l) 0 := by
    filter_upwards [continuousCubeMeasure_ae_mem n] with x hx
    simp only [v,V,hηK x (hcube hx),one_pow,one_mul]
  have hbeq : (fun x => ‖b x‖)=ᵐ[μ](fun x => if k<u x∧u x≤l then ‖g x‖ else 0) := by
    filter_upwards [continuousCubeMeasure_ae_mem n] with x hx
    have he : b x=(if k<u x then g x else 0)-(if l<u x then g x else 0) := by
      simp only [b,G,hηK x (hcube hx),hηg x (hcube hx),one_pow,one_smul,smul_zero,add_zero]
    rw [he]
    by_cases hk : k<u x
    · by_cases hl : l<u x
      · simp [hk,hl,not_le.mpr hl]
      · simp [hk,hl,le_of_not_gt hl]
    · have hl : ¬l<u x := not_lt.mpr (le_trans (le_of_not_gt hk) hkl)
      simp [hk,hl]
  have hzv : ∀ᵐ x ∂μ.restrict Z,v x=0 := by
    filter_upwards [hz,ae_restrict_of_ae hveq] with x hx he
    rw [he,max_eq_right (sub_nonpos.mpr hx),max_eq_right (sub_nonpos.mpr (hx.trans hkl)),sub_self]
  have hrel := hvb.cube_zero_set_poincare hZ hzv
  have hHpoint : (H.indicator (fun _ : Space n => l-k))≤ᵐ[μ](fun x => ‖v x‖) := by
    have ha : ∀ᵐ x ∂μ,x∈H → l≤u x := (ae_restrict_iff' hH).mp hh
    filter_upwards [ha,hveq] with x hx he
    by_cases hxh : x∈H
    · rw [indicator_of_mem hxh,he,max_eq_left (sub_nonneg.mpr ((hkl.trans (hx hxh)))),
        max_eq_left (sub_nonneg.mpr (hx hxh))]
      have hid : (u x-k)-(u x-l)=l-k := by ring
      rw [hid,Real.norm_of_nonneg (sub_nonneg.mpr hkl)]
    · rw [indicator_of_notMem hxh]
      exact norm_nonneg _
  have hi : Integrable (H.indicator (fun _ : Space n => l-k)) μ :=
    (integrable_const (l-k)).indicator hH
  have hlow : (l-k)*(μ H).toReal≤∫ x,‖v x‖ ∂μ := by
    have hm := integral_mono_ae hi hvμ.norm hHpoint
    simpa only [integral_indicator hH,integral_const,measureReal_def,
      Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hm
  rw [integral_congr_ae hbeq] at hrel
  have hm := mul_le_mul_of_nonneg_left hlow (ENNReal.toReal_nonneg (a:=μ Z))
  exact (by nlinarith only [hm] : (l-k)*(μ Z).toReal*(μ H).toReal≤
    (μ Z).toReal*(∫ x,‖v x‖ ∂μ)).trans hrel

end BMCompactPDE

end ContinuousBody_ContinuousBand

#print axioms BMCompactPDE.continuousUnitCube_measurable
#print axioms BMCompactPDE.continuousCubeMeasure_eq
#print axioms BMCompactPDE.continuousCubeMeasure_le_volume
#print axioms BMCompactPDE.continuousCubeMeasure_ae_mem
#print axioms BMCompactPDE.continuousAffineCubeMeasure_le_volume
#print axioms BMCompactPDE.SobolevPair.exists_smooth_L1_approx_of_measure_le
#print axioms BMCompactPDE.SobolevPair.cube_pair_poincare
#print axioms BMCompactPDE.SobolevPair.cube_zero_set_poincare
#print axioms BMCompactPDE.SobolevPair.cube_pair_poincare_local
#print axioms BMCompactPDE.SobolevPair.affine_cube_pair_poincare
#print axioms BMCompactPDE.exists_uniform_scaled_cutoff
#print axioms BMCompactPDE.SobolevPair.cube_level_band_poincare
