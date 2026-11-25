import RegCaccioppoliAlgebra

/-! Actual weak Caccioppoli energy estimate. Integrability is derived from the
local Sobolev data and genuine smooth compact cutoff. The explicitly displayed
cutoff-product W0 pair is the test-admissibility input; a generic nonsmooth
multiplier/density theorem will supply it for integer cutoff exponents. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

theorem WeakPHarmonicPair.caccioppoli_of_cutoff_W0
    {n : ℕ} {p m : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hm : p ≤ m) (k : ℝ)
    (htest : ZeroBoundarySobolevPair p D
      (fun x => η x ^ m * (u x-k))
      (fun x => η x ^ m • g x +
        (m * η x ^ (m-1) * (u x-k)) • gradient η x)) :
    (∫ x in D, η x ^ m * ‖g x‖ ^ p) ≤
      m^p * ∫ x in D, |u x-k|^p * ‖gradient η x‖^p := by
  have hp0 : 0 < p := zero_lt_one.trans hu.1
  have hm0 : 0 ≤ m := hp0.le.trans hm
  let μ := volume.restrict D
  let A : Space n → ℝ := fun x => η x^m * ‖g x‖^p
  let B : Space n → ℝ := fun x => |u x-k|^p * ‖gradient η x‖^p
  let C : Space n → ℝ := fun x =>
    m * η x^(m-1) * (u x-k) * inner ℝ (pFlux p (g x)) (gradient η x)
  let W : Space n → Space n := fun x => η x^m • g x +
    (m * η x^(m-1) * (u x-k)) • gradient η x
  have hg := (hu.2.2.1 D hD).2.2.1
  have hGI := integrable_norm_rpow_of_memLp hu.1 hg
  have hηm : Continuous (fun x => η x^m) :=
    hη.1.continuous.rpow_const (fun _ => Or.inr hm0)
  have hAI : Integrable A μ := by
    apply hGI.mono_nonneg (hηm.aestronglyMeasurable.mul hGI.1)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (Real.rpow_nonneg (hη0 x) _) (Real.rpow_nonneg (norm_nonneg (g x)) _))
    · exact Eventually.of_forall (fun x => by
        have he : η x^m ≤ 1 := Real.rpow_le_one (hη0 x) (hη1 x) hm0
        exact (mul_le_mul_of_nonneg_right he
          (Real.rpow_nonneg (norm_nonneg (g x)) p)).trans_eq (one_mul _))
  have hgrad : Continuous (gradient η) :=
    BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1
  obtain ⟨c,hc⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).exists_bound_of_continuous hgrad
  let c' : ℝ := max c 0
  have hc0 : 0 ≤ c' := le_max_right _ _
  have hcb (x : Space n) : ‖gradient η x‖ ≤ c' := (hc x).trans (le_max_left _ _)
  have hz := ((hu.sub_const k).2.2.1 D hD).2.1
  have hzI : Integrable (fun x => |u x-k|^p) μ := by
    simpa only [Real.norm_eq_abs,ENNReal.toReal_ofReal hp0.le] using
      hz.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hgradp : Continuous (fun x => ‖gradient η x‖^p) :=
    hgrad.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hBI : Integrable B μ := by
    apply (hzI.mul_const (c'^p)).mono_nonneg (hzI.1.mul hgradp.aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (Real.rpow_nonneg (abs_nonneg (u x-k)) _) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hcb x) hp0.le)
        (Real.rpow_nonneg (abs_nonneg (u x-k)) _))
  obtain ⟨hFI,hFzero⟩ := hu.2.2.2 D hD _ W htest
  have hdecomp : fluxPairing p g W = A+C := by
    funext x
    simp only [fluxPairing,W,A,C,Pi.add_apply,inner_add_right,inner_smul_right,
      pFlux_inner_self hu.1]
  have hCI : Integrable C μ := by
    have hh := hFI.sub hAI
    simpa only [hdecomp,Pi.sub_apply,Pi.add_apply,add_sub_cancel_left] using! hh
  rw [hdecomp] at hFzero
  simp only [Pi.add_apply] at hFzero
  rw [integral_add hAI hCI] at hFzero
  have hb := integral_mono hCI.neg
    ((hAI.const_mul ((p-1)/p)).add (hBI.const_mul (m^p/p)))
    (fun x => cutoff_flux_cross_absorption hu.1 hm (hη0 x) (hη1 x)
      (g x) (gradient η x) (z := u x-k))
  simp only [Pi.neg_apply,Pi.add_apply] at hb
  rw [integral_neg,integral_add (hAI.const_mul ((p-1)/p)) (hBI.const_mul (m^p/p)),
    integral_const_mul,integral_const_mul] at hb
  have hcint : (∫ x, C x ∂μ) = -(∫ x, A x ∂μ) := by linarith
  rw [hcint,neg_neg] at hb
  have hmul := mul_le_mul_of_nonneg_left hb hp0.le
  have hα : p*((p-1)/p)=p-1 := by field_simp
  have hβ : p*(m^p/p)=m^p := by field_simp
  rw [mul_add,←mul_assoc,hα,←mul_assoc,hβ] at hmul
  change (∫ x, A x ∂μ) ≤ m^p * ∫ x, B x ∂μ
  nlinarith

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.caccioppoli_of_cutoff_W0
