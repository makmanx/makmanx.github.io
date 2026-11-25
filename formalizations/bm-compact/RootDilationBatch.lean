import GradientAnalyticBatch
import CapacityAffineEnergy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

section DilationBody_RootDilationMeasure

/-! Actual Lebesgue change of variables for spatial dilation.  The measure
factor is retained explicitly; no weak-PDE transformation is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace BMCompactPDE

def spatialDilationJacobian (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |(R^n)⁻¹|

theorem measurePreserving_dilation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) {R : ℝ} (hR : R≠0) :
    MeasurePreserving (fun x : Space n => R • x)
      (volume.restrict ((fun x => R • x) ⁻¹' D))
      (spatialDilationJacobian n R • volume.restrict D) := by
  refine ⟨measurable_const_smul R,?_⟩
  rw [←Measure.restrict_map (measurable_const_smul R) hD,
    Measure.map_addHaar_smul volume hR,Measure.restrict_smul]
  simp only [spatialDilationJacobian,Space,finrank_euclideanSpace,Fintype.card_fin]

theorem eLpNorm_comp_dilation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) {R : ℝ} (hR : R≠0)
    {E : Type*} [NormedAddCommGroup E] {f : Space n → E}
    (hf : AEStronglyMeasurable f (volume.restrict D))
    {q : ℝ≥0∞} (hqt : q≠∞) :
    eLpNorm (fun x => f (R • x)) q
      (volume.restrict ((fun x => R • x) ⁻¹' D)) =
      (spatialDilationJacobian n R)^((1/q).toReal) *
        eLpNorm f q (volume.restrict D) := by
  have ht := measurePreserving_dilation_restrict hD hR
  have he := eLpNorm_comp_measurePreserving (p := q)
    (hf.smul_measure (spatialDilationJacobian n R)) ht
  simpa only [Function.comp_def,eLpNorm_smul_measure_of_ne_top hqt,smul_eq_mul] using he

theorem MemLp.comp_dilation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) {R : ℝ} (hR : R≠0)
    {E : Type*} [NormedAddCommGroup E] {f : Space n → E} {q : ℝ≥0∞}
    (hf : MemLp f q (volume.restrict D)) :
    MemLp (fun x => f (R • x)) q
      (volume.restrict ((fun x => R • x) ⁻¹' D)) := by
  exact (hf.smul_measure (by simp [spatialDilationJacobian])).comp_measurePreserving
    (measurePreserving_dilation_restrict hD hR)

theorem integrable_comp_dilation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) {R : ℝ} (hR : R≠0)
    {E : Type*} [NormedAddCommGroup E] {f : Space n → E}
    (hf : Integrable f (volume.restrict D)) :
    Integrable (fun x => f (R • x))
      (volume.restrict ((fun x => R • x) ⁻¹' D)) := by
  exact (measurePreserving_dilation_restrict hD hR).integrable_comp_of_integrable
    (hf.smul_measure (by simp [spatialDilationJacobian]))

theorem integral_comp_dilation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) {R : ℝ} (hR : R≠0)
    (f : Space n → ℝ) :
    (∫ x in ((fun x => R • x) ⁻¹' D),f (R • x)) =
      |(R^n)⁻¹| * ∫ x in D,f x := by
  have hemb : MeasurableEmbedding (fun x : Space n => R • x) :=
    (Homeomorph.smul (Units.mk0 R hR)).measurableEmbedding
  rw [(measurePreserving_dilation_restrict hD hR).integral_comp hemb f,
    integral_smul_measure]
  simp only [spatialDilationJacobian,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul]

end BMCompactPDE
end
end DilationBody_RootDilationMeasure

section DilationBody_RootDilationSobolev

/-! Dilation of actual distributional Sobolev pairs and their genuine W0
approximants. The weak gradient acquires the spatial scale factor R. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology Pointwise
namespace BMCompactPDE

theorem SmoothTest.dilation_actual {n : ℕ} {D : Set (Space n)}
    {φ : Space n → ℝ} (hφ : SmoothTest D φ) {R : ℝ} (hR : R≠0) :
    SmoothTest ((fun x => R • x) ⁻¹' D) (fun x => φ (R • x)) := by
  refine ⟨hφ.1.comp (contDiff_id.const_smul R),
    hφ.2.1.comp_homeomorph (Homeomorph.smul (Units.mk0 R hR)),?_⟩
  intro x hx
  exact hφ.2.2 (tsupport_comp_subset_preimage φ (continuous_const_smul R) hx)

theorem SobolevPair.dilation_actual {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hD : MeasurableSet D) {R : ℝ} (hR : R≠0) :
    SobolevPair p ((fun x => R • x) ⁻¹' D)
      (fun x => u (R • x)) (fun x => R • g (R • x)) := by
  refine ⟨hu.1,MemLp.comp_dilation_restrict hD hR hu.2.1,
    (MemLp.comp_dilation_restrict hD hR hu.2.2.1).const_smul R,?_⟩
  intro φ hφ i
  let ψ := fun y : Space n => φ (R⁻¹ • y)
  have hψ : SmoothTest D ψ := by
    have hs := hφ.dilation_actual (inv_ne_zero hR)
    refine ⟨hs.1,hs.2.1,?_⟩
    intro y hy
    have hh := hs.2.2 hy
    change R • (R⁻¹ • y)∈D at hh
    simpa only [smul_smul,mul_inv_cancel₀ hR,one_smul] using hh
  have hgrad (x : Space n) : gradient ψ (R • x)=R⁻¹ • gradient φ x := by
    dsimp only [ψ]
    rw [BMCompactCapacityV2.gradient_comp_const_smul hφ.1,smul_smul,
      inv_mul_cancel₀ hR,one_smul]
  obtain ⟨hi,hj,he⟩ := hu.2.2.2 ψ hψ i
  have hL : (fun x => u (R • x)*(gradient φ x) i)=
      (fun x => R*(u (R • x)*(gradient ψ (R • x)) i)) := by
    funext x
    rw [hgrad]
    simp only [PiLp.smul_apply,smul_eq_mul]
    field_simp [hR]
  have hRt : (fun x => (R • g (R • x)) i*φ x)=
      (fun x => R*((g (R • x)) i*ψ (R • x))) := by
    funext x
    simp only [ψ,smul_smul,inv_mul_cancel₀ hR,one_smul,PiLp.smul_apply,smul_eq_mul]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [hL]
    exact (integrable_comp_dilation_restrict hD hR hi).const_mul R
  · rw [hRt]
    exact (integrable_comp_dilation_restrict hD hR hj).const_mul R
  · have hIL := integral_comp_dilation_restrict hD hR
      (fun y => u y*(gradient ψ y) i)
    have hIR := integral_comp_dilation_restrict hD hR
      (fun y => (g y) i*ψ y)
    rw [hL,hRt,integral_const_mul,integral_const_mul,hIL,hIR,he]
    ring

theorem ZeroBoundarySobolevPair.dilation_actual {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hD : MeasurableSet D)
    {R : ℝ} (hR : R≠0) :
    ZeroBoundarySobolevPair p ((fun x => R • x) ⁻¹' D)
      (fun x => u (R • x)) (fun x => R • g (R • x)) := by
  obtain ⟨su,φ,hφ,hφu,hφg⟩ := hu
  let q := ENNReal.ofReal p
  let J := (spatialDilationJacobian n R)^((1/q).toReal)
  have hJ : J≠(∞ : ℝ≥0∞) := by
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (by simp [spatialDilationJacobian])
  refine ⟨su.dilation_actual hD hR,fun j x => φ j (R • x),
    fun j => (hφ j).dilation_actual hR,?_,?_⟩
  · have hh := ENNReal.Tendsto.const_mul hφu (Or.inr hJ)
    simp only [mul_zero] at hh
    convert hh using 1
    funext j
    exact eLpNorm_comp_dilation_restrict hD hR
      (((hφ j).sobolevPair su.1).2.1.sub su.2.1).1 ENNReal.ofReal_ne_top
  · have hh := ENNReal.Tendsto.const_mul hφg (Or.inr hJ)
    simp only [mul_zero] at hh
    have hh' := ENNReal.Tendsto.const_mul hh (a := ‖R‖ₑ) (Or.inr enorm_ne_top)
    simp only [mul_zero] at hh'
    convert hh' using 1
    funext j
    have he : (fun x => gradient (fun y => φ j (R • y)) x-R • g (R • x))=
        R • (fun x => gradient (φ j) (R • x)-g (R • x)) := by
      funext x
      rw [BMCompactCapacityV2.gradient_comp_const_smul (hφ j).1]
      simp only [Pi.smul_apply,smul_sub]
    rw [he,eLpNorm_const_smul]
    have hnorm := eLpNorm_comp_dilation_restrict hD hR
      (f := fun x => gradient (φ j) x-g x) (q := ENNReal.ofReal p)
      (((hφ j).sobolevPair su.1).2.2.1.sub su.2.2.1).1 ENNReal.ofReal_ne_top
    simpa only [J,q] using congrArg (fun z : ℝ≥0∞ => ‖R‖ₑ*z) hnorm

theorem LocalDomain.dilation_actual {n : ℕ} {D Ω : Set (Space n)}
    (hD : LocalDomain D Ω) {R : ℝ} (hR : R≠0) :
    LocalDomain ((fun x => R • x) ⁻¹' D) ((fun x => R • x) ⁻¹' Ω) := by
  let T := Homeomorph.smul (Units.mk0 R hR) (α := Space n)
  refine ⟨hD.1.preimage (continuous_const_smul R),?_,?_⟩
  · have he : ((fun x : Space n => R • x) ⁻¹' D)=R⁻¹ • D := by
      rw [←preimage_smul_inv₀ (inv_ne_zero hR),inv_inv]
    rw [he]
    exact hD.2.1.smul₀ R⁻¹
  · have hc : closure ((fun x : Space n => R • x) ⁻¹' D)=
        (fun x => R • x) ⁻¹' closure D := by
      exact (T.preimage_closure D).symm
    rw [hc]
    exact preimage_mono hD.2.2

end BMCompactPDE
end
end DilationBody_RootDilationSobolev

section DilationBody_RootDilationSource

/-! Actual spatial scaling of the full constant-source weak PDE.  Both the
Sobolev field and every W0 test are transformed; the source is R^p*c. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

theorem WeakPSourcePair.dilation_actual {n : ℕ} {p c : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) {R : ℝ} (hR : 0<R) :
    WeakPSourcePair p (R^p*c) ((fun x => R • x) ⁻¹' Ω)
      (fun x => u (R • x)) (fun x => R • g (R • x)) := by
  have hd {D : Set (Space n)} (hD : LocalDomain D ((fun x => R • x) ⁻¹' Ω)) :
      LocalDomain ((fun y => R⁻¹ • y) ⁻¹' D) Ω := by
    simpa only [preimage_preimage,Function.comp_def,smul_smul,
      mul_inv_cancel₀ hR.ne',one_smul,preimage_id'] using
      hD.dilation_actual (inv_ne_zero hR.ne')
  refine ⟨hu.1,hu.2.1.preimage (continuous_const_smul R),?_,?_⟩
  · intro D hD
    have hs := (hu.2.2.1 _ (hd hD)).dilation_actual
      (hd hD).1.measurableSet hR.ne'
    simpa only [preimage_preimage,Function.comp_def,smul_smul,
      inv_mul_cancel₀ hR.ne',one_smul,preimage_id'] using hs
  · intro D hD θ k hθ
    let D' : Set (Space n) := (fun y => R⁻¹ • y) ⁻¹' D
    let θ' : Space n → ℝ := fun y => θ (R⁻¹ • y)
    let k' : Space n → Space n := fun y => R⁻¹ • k (R⁻¹ • y)
    have hθ' : ZeroBoundarySobolevPair p D' θ' k' :=
      hθ.dilation_actual hD.1.measurableSet (inv_ne_zero hR.ne')
    obtain ⟨hi,he⟩ := hu.2.2.2 D' (hd hD) θ' k' hθ'
    have hF : fluxPairing p (fun x => R • g (R • x)) k=
        (fun x => R^p*fluxPairing p g k' (R • x)) := by
      have hpow : R^p=R^(p-2)*R*R := by
        calc
          R^p = R^((p-2)+2) := by congr 1;ring
          _ = R^(p-2)*R^2 := Real.rpow_add hR _ _
          _ = _ := by rw [Real.rpow_two];ring
      have hcoef : R^p*R⁻¹=R^(p-2)*R := by rw [hpow];field_simp
      funext x
      simp only [fluxPairing,k',smul_smul,inv_mul_cancel₀ hR.ne',one_smul,
        pFlux_smul,real_inner_smul_left,real_inner_smul_right,abs_of_pos hR]
      rw [←mul_assoc,hcoef]
    have hcomp : Integrable (fun x => fluxPairing p g k' (R • x)) (volume.restrict D) := by
      have ht := integrable_comp_dilation_restrict (hd hD).1.measurableSet hR.ne' hi
      simpa only [D',preimage_preimage,Function.comp_def,smul_smul,
        inv_mul_cancel₀ hR.ne',one_smul,preimage_id'] using ht
    have hfluxInt : (∫ x in D,fluxPairing p g k' (R • x))=
        |(R^n)⁻¹| * (∫ x in D',fluxPairing p g k' x) := by
      have ht := integral_comp_dilation_restrict (hd hD).1.measurableSet hR.ne'
        (fluxPairing p g k')
      simpa only [D',preimage_preimage,Function.comp_def,smul_smul,
        inv_mul_cancel₀ hR.ne',one_smul,preimage_id'] using ht
    have hθInt : (∫ x in D,θ x)=|(R^n)⁻¹| * (∫ x in D',θ' x) := by
      have ht := integral_comp_dilation_restrict (hd hD).1.measurableSet hR.ne' θ'
      simpa only [D',θ',preimage_preimage,Function.comp_def,smul_smul,
        inv_mul_cancel₀ hR.ne',one_smul,preimage_id'] using ht
    rw [hF]
    refine ⟨hcomp.const_mul _,?_⟩
    rw [integral_const_mul,hfluxInt,he,hθInt]
    ring

theorem WeakPSourcePair.affine_domain_actual {n : ℕ} {p c : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (a : Space n) {R : ℝ} (hR : 0<R) :
    WeakPSourcePair p (R^p*c) ((fun x => a+R • x) ⁻¹' Ω)
      (fun x => u (a+R • x)) (fun x => R • g (a+R • x)) := by
  simpa only [preimage_preimage,Function.comp_def,add_comm] using
    (hu.translate_actual a).dilation_actual hR

end BMCompactPDE
end
end DilationBody_RootDilationSource

#print axioms BMCompactPDE.measurePreserving_dilation_restrict
#print axioms BMCompactPDE.eLpNorm_comp_dilation_restrict
#print axioms BMCompactPDE.MemLp.comp_dilation_restrict
#print axioms BMCompactPDE.integrable_comp_dilation_restrict
#print axioms BMCompactPDE.integral_comp_dilation_restrict
#print axioms BMCompactPDE.SmoothTest.dilation_actual
#print axioms BMCompactPDE.SobolevPair.dilation_actual
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.dilation_actual
#print axioms BMCompactPDE.LocalDomain.dilation_actual
#print axioms BMCompactPDE.WeakPSourcePair.dilation_actual
#print axioms BMCompactPDE.WeakPSourcePair.affine_domain_actual
