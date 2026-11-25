import GradientEnergy
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FunProp

section GradientBody_GradientTranslation

/-! Translation of the actual distributional Sobolev graph.  The independently
supplied weak gradient is translated with the function; no classical derivative
of a weak solution is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

theorem gradient_comp_add_actual {n : ℕ} (f : Space n → ℝ) (a x : Space n) :
    gradient (fun y => f (y+a)) x=gradient f (x+a) := by
  unfold gradient
  rw [fderiv_comp_add_right]

theorem measurePreserving_translation_restrict {n : ℕ} {D : Set (Space n)}
    (hD : MeasurableSet D) (a : Space n) :
    MeasurePreserving (fun x => x+a)
      (volume.restrict ((fun x => x+a) ⁻¹' D)) (volume.restrict D) := by
  refine ⟨measurable_id.add measurable_const,?_⟩
  rw [← Measure.restrict_map (f := fun x : Space n => x+a)
    (measurable_id.add measurable_const) hD]
  rw [(measurePreserving_add_right (volume : Measure (Space n)) a).map_eq]

theorem SmoothTest.translate_actual {n : ℕ} {D : Set (Space n)}
    {f : Space n → ℝ} (hf : SmoothTest D f) (a : Space n) :
    SmoothTest ((fun x => x+a) ⁻¹' D) (fun x => f (x+a)) := by
  refine ⟨hf.1.comp (contDiff_id.add contDiff_const),?_,?_⟩
  · exact hf.2.1.comp_homeomorph (Homeomorph.addRight a)
  · intro x hx
    exact hf.2.2 (tsupport_comp_subset_preimage f
      (continuous_id.add continuous_const) hx)

theorem SobolevPair.translate_actual {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hD : MeasurableSet D) (a : Space n) :
    SobolevPair p ((fun x => x+a) ⁻¹' D) (fun x => u (x+a)) (fun x => g (x+a)) := by
  let S := (fun x : Space n => x+a) ⁻¹' D
  have ht := measurePreserving_translation_restrict hD a
  refine ⟨hu.1,hu.2.1.comp_measurePreserving ht,
    hu.2.2.1.comp_measurePreserving ht,?_⟩
  intro φ hφ i
  let ψ := fun y : Space n => φ (y-a)
  have hψ : SmoothTest D ψ := by
    have hs := hφ.translate_actual (-a)
    refine ⟨hs.1,hs.2.1,?_⟩
    intro y hy
    have hh := hs.2.2 hy
    change (y+-a)+a∈D at hh
    simpa only [neg_add_cancel_right] using hh
  have hgrad (x : Space n) : gradient ψ (x+a)=gradient φ x := by
    change gradient (fun y => φ (y+-a)) (x+a)=gradient φ x
    rw [gradient_comp_add_actual]
    simp only [add_neg_cancel_right]
  obtain ⟨hi,hj,he⟩ := hu.2.2.2 ψ hψ i
  have hemb : MeasurableEmbedding (fun x : Space n => x+a) :=
    (Homeomorph.addRight a).measurableEmbedding
  have hL : (fun x => (u (x+a)) * (gradient φ x) i)=
      (fun y => u y*(gradient ψ y) i) ∘ (fun x => x+a) := by
    funext x
    simp only [Function.comp_apply,hgrad]
  have hR : (fun x => (g (x+a)) i * φ x)=
      (fun y => (g y) i*ψ y) ∘ (fun x => x+a) := by
    funext x
    simp only [Function.comp_apply,ψ,add_sub_cancel_right]
  refine ⟨?_,?_,?_⟩
  · rw [hL]
    exact ht.integrable_comp_of_integrable hi
  · rw [hR]
    exact ht.integrable_comp_of_integrable hj
  · rw [hL,hR]
    simp only [Function.comp_def]
    rw [ht.integral_comp hemb (fun y => u y*(gradient ψ y) i),
      ht.integral_comp hemb (fun y => (g y) i*ψ y)]
    exact he

theorem ZeroBoundarySobolevPair.translate_actual {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hD : MeasurableSet D) (a : Space n) :
    ZeroBoundarySobolevPair p ((fun x => x+a) ⁻¹' D)
      (fun x => u (x+a)) (fun x => g (x+a)) := by
  obtain ⟨su,φ,hφ,hφu,hφg⟩ := hu
  have ht := measurePreserving_translation_restrict hD a
  refine ⟨su.translate_actual hD a,fun j x => φ j (x+a),
    fun j => (hφ j).translate_actual a,?_,?_⟩
  · have he (j : ℕ) : eLpNorm ((fun x => φ j (x+a))-(fun x => u (x+a)))
        (ENNReal.ofReal p) (volume.restrict ((fun x => x+a) ⁻¹' D))=
        eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict D) :=
      eLpNorm_comp_measurePreserving (((hφ j).sobolevPair su.1).2.1.sub su.2.1).1 ht
    simpa only [he] using hφu
  · have he (j : ℕ) : eLpNorm
        (fun x => gradient (fun y => φ j (y+a)) x-g (x+a))
        (ENNReal.ofReal p) (volume.restrict ((fun x => x+a) ⁻¹' D))=
        eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p)
          (volume.restrict D) := by
      simp only [gradient_comp_add_actual]
      exact eLpNorm_comp_measurePreserving
        (((hφ j).sobolevPair su.1).2.2.1.sub su.2.2.1).1 ht
    simpa only [he] using hφg

theorem LocalDomain.translate_actual {n : ℕ} {D Ω : Set (Space n)}
    (hD : LocalDomain D Ω) (a : Space n) :
    LocalDomain ((fun x => x+a) ⁻¹' D) ((fun x => x+a) ⁻¹' Ω) := by
  refine ⟨hD.1.preimage (continuous_id.add continuous_const),
    (isometry_add_right a).antilipschitz.isBounded_preimage hD.2.1,?_⟩
  have hc : closure ((fun x : Space n => x+a) ⁻¹' D)=
      (fun x => x+a) ⁻¹' closure D := by
    simpa only [Homeomorph.coe_addRight] using
      ((Homeomorph.addRight a).preimage_closure D).symm
  rw [hc]
  exact preimage_mono hD.2.2

/-- The constant-source weak PDE is invariant under spatial translation, tested
against the actual translated full W0 graph, including on unbounded domains. -/
theorem WeakPSourcePair.translate_actual {n : ℕ} {p c : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (a : Space n) :
    WeakPSourcePair p c ((fun x => x+a) ⁻¹' Ω)
      (fun x => u (x+a)) (fun x => g (x+a)) := by
  have hd {D : Set (Space n)} (hD : LocalDomain D ((fun x => x+a) ⁻¹' Ω)) :
      LocalDomain ((fun y => y+-a) ⁻¹' D) Ω := by
    simpa only [preimage_preimage,Function.comp_def,neg_add_cancel_right,
      preimage_id'] using hD.translate_actual (-a)
  refine ⟨hu.1,hu.2.1.preimage (continuous_id.add continuous_const),?_,?_⟩
  · intro D hD
    have hs := (hu.2.2.1 _ (hd hD)).translate_actual
      (hd hD).1.measurableSet a
    simpa only [preimage_preimage,Function.comp_def,add_neg_cancel_right,
      preimage_id'] using hs
  · intro D hD θ k hθ
    have hθ' := hθ.translate_actual hD.1.measurableSet (-a)
    obtain ⟨hi,he⟩ := hu.2.2.2 _ (hd hD)
      (fun y => θ (y+-a)) (fun y => k (y+-a)) hθ'
    have ht := measurePreserving_translation_restrict (hd hD).1.measurableSet a
    have ht' : MeasurePreserving (fun x => x+a) (volume.restrict D)
        (volume.restrict ((fun y => y+-a) ⁻¹' D)) := by
      simpa only [preimage_preimage,Function.comp_def,add_neg_cancel_right,
        preimage_id'] using ht
    have hemb : MeasurableEmbedding (fun x : Space n => x+a) :=
      (Homeomorph.addRight a).measurableEmbedding
    have hflux : fluxPairing p (fun x => g (x+a)) k=
        (fluxPairing p g (fun y => k (y+-a))) ∘ (fun x => x+a) := by
      funext x
      simp only [fluxPairing,Function.comp_apply,add_neg_cancel_right]
    refine ⟨?_,?_⟩
    · rw [hflux]
      exact ht'.integrable_comp_of_integrable hi
    · rw [hflux]
      simp only [Function.comp_def]
      rw [ht'.integral_comp hemb,he]
      congr 1
      have hh := ht'.integral_comp hemb (fun y => θ (y+-a))
      simpa only [add_neg_cancel_right] using hh.symm

end BMCompactPDE
#print axioms BMCompactPDE.gradient_comp_add_actual
#print axioms BMCompactPDE.measurePreserving_translation_restrict
#print axioms BMCompactPDE.SmoothTest.translate_actual
#print axioms BMCompactPDE.SobolevPair.translate_actual
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.translate_actual
#print axioms BMCompactPDE.LocalDomain.translate_actual
#print axioms BMCompactPDE.WeakPSourcePair.translate_actual

end -- exact source's anonymous noncomputable section
end GradientBody_GradientTranslation

section GradientBody_GradientSingularFlux

/-! The singular-range flux coercivity needed in the actual difference-quotient
argument. This is the p-Laplace specialization of the monotonicity step in
Tolksdorf1984, Lemma1. It is derived from the actual power function and inner
product; neither a coercivity class nor a desired gradient estimate is assumed. -/
noncomputable section
set_option autoImplicit false
open Set InnerProductSpace
namespace BMCompactPDE

private theorem radial_coercivity_ordered {p r s : ℝ}
    (hp : 1<p) (hp2 : p≤2) (hr : 0≤r) (hs : r≤s) :
    (p-1)*(r+s)^(p-2)*(s-r)^2≤(s^(p-1)-r^(p-1))*(s-r) := by
  rcases hs.eq_or_lt with he|hlt
  · subst s
    simp only [sub_self,pow_two,mul_zero]
    exact le_rfl
  have hsp : 0<s := hr.trans_lt hlt
  have hc := Real.concaveOn_rpow (by linarith : 0≤p-1) (by linarith : p-1≤1)
  have hd := Real.hasDerivAt_rpow_const (p := p-1) (Or.inl hsp.ne')
  have hsec := hc.le_slope_of_hasDerivAt hr (hr.trans hlt.le) hlt hd
  have hpow : p-1-1=p-2 := by ring
  rw [hpow,slope_def_field] at hsec
  have hlin := (le_div_iff₀ (sub_pos.mpr hlt)).mp hsec
  have hquad := mul_le_mul_of_nonneg_right hlin (sub_nonneg.mpr hlt.le)
  have hw := Real.rpow_le_rpow_of_nonpos hsp
    (show s≤r+s by linarith only [hr]) (by linarith : p-2≤0)
  have hweight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw (by linarith : 0≤p-1)) (sq_nonneg (s-r))
  nlinarith only [hquad,hweight]

theorem rpow_radial_singular_coercivity {p r s : ℝ}
    (hp : 1<p) (hp2 : p≤2) (hr : 0≤r) (hs : 0≤s) :
    (p-1)*(r+s)^(p-2)*(r-s)^2≤(r^(p-1)-s^(p-1))*(r-s) := by
  rcases le_total r s with h|h
  · have hh := radial_coercivity_ordered hp hp2 hr h
    nlinarith only [hh]
  · have hh := radial_coercivity_ordered hp hp2 hs h
    rw [add_comm s r] at hh
    exact hh

private theorem power_weight_square {p r : ℝ} (hp : 1<p) (hr : 0≤r) :
    r^(p-2)*r^2=r^p := by
  rw [pow_two,← mul_assoc,rpow_coefficient_mul hp hr,
    ← Real.rpow_add_one' hr (by linarith : p-1+1≠0)]
  congr 1
  ring

theorem pFlux_pairing_controls_weighted_difference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℝ} (hp : 1<p) (hp2 : p≤2) (v w : E) :
    (p-1)*(‖v‖+‖w‖)^(p-2)*‖v-w‖^2≤
      inner ℝ (pFlux p v-pFlux p w) (v-w) := by
  by_cases hv : v=0
  · subst v
    simp only [norm_zero,zero_add,zero_sub,norm_neg,pFlux_zero,inner_neg_neg]
    rw [pFlux_inner_self hp,mul_assoc,power_weight_square hp (norm_nonneg w)]
    have hh := mul_le_mul_of_nonneg_right (show p-1≤1 by linarith)
      (Real.rpow_nonneg (norm_nonneg w) p)
    simpa only [one_mul] using hh
  by_cases hw : w=0
  · subst w
    simp only [norm_zero,add_zero,sub_zero,pFlux_zero]
    rw [pFlux_inner_self hp,mul_assoc,power_weight_square hp (norm_nonneg v)]
    have hh := mul_le_mul_of_nonneg_right (show p-1≤1 by linarith)
      (Real.rpow_nonneg (norm_nonneg v) p)
    simpa only [one_mul] using hh
  let r := ‖v‖
  let s := ‖w‖
  let z := inner ℝ v w
  let A := r^(p-2)
  let B := s^(p-2)
  let W := (p-1)*(r+s)^(p-2)
  have hr : 0<r := norm_pos_iff.mpr hv
  have hs : 0<s := norm_pos_iff.mpr hw
  have hz : 0≤r*s-z := sub_nonneg.mpr (real_inner_le_norm v w)
  have hrad := rpow_radial_singular_coercivity hp hp2 hr.le hs.le
  have ha : (r+s)^(p-2)≤A := Real.rpow_le_rpow_of_nonpos hr
    (le_add_of_nonneg_right hs.le) (by linarith : p-2≤0)
  have hb : (r+s)^(p-2)≤B := Real.rpow_le_rpow_of_nonpos hs
    (le_add_of_nonneg_left hr.le) (by linarith : p-2≤0)
  have hW : W≤(r+s)^(p-2) := by
    have hh := mul_le_mul_of_nonneg_right (show p-1≤1 by linarith)
      (Real.rpow_nonneg (add_nonneg hr.le hs.le) (p-2))
    simpa only [one_mul] using hh
  have hcoef : 2*W≤A+B := by linarith only [ha,hb,hW]
  have hang := mul_le_mul_of_nonneg_right hcoef hz
  have hD : inner ℝ (pFlux p v-pFlux p w) (v-w)=
      (r^(p-1)-s^(p-1))*(r-s)+(A+B)*(r*s-z) := by
    have hrpow := rpow_coefficient_mul hp hr.le
    have hspow := rpow_coefficient_mul hp hs.le
    dsimp only [A,B,r,s,z] at *
    simp only [pFlux,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_self_eq_norm_mul_norm,real_inner_comm w v]
    rw [← hrpow,← hspow]
    ring
  have hnorm : ‖v-w‖^2=(r-s)^2+2*(r*s-z) := by
    rw [norm_sub_sq_real]
    dsimp only [r,s,z]
    ring
  rw [hD,hnorm]
  change W*((r-s)^2+2*(r*s-z))≤_
  change W*(r-s)^2≤_ at hrad
  nlinarith only [hrad,hang]

end BMCompactPDE
#print axioms BMCompactPDE.rpow_radial_singular_coercivity
#print axioms BMCompactPDE.pFlux_pairing_controls_weighted_difference

end -- exact source's anonymous noncomputable section
end GradientBody_GradientSingularFlux

section GradientBody_GradientDifference

/-! Actual spatial finite differences and local flux identities.  All test
functions below are constructed in the concrete W0 graph from the weak pairs.
No Hessian, selected continuous gradient or regularity conclusion is an input. -/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.mono_actual {n : ℕ} {p c : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hU : U⊆Ω) (hUo : IsOpen U) :
    WeakPSourcePair p c U u g := by
  refine ⟨hu.1,hUo,hu.2.2.1.mono hU,?_⟩
  intro D hD θ k hθ
  exact hu.2.2.2 D ⟨hD.1,hD.2.1,hD.2.2.trans hU⟩ θ k hθ

/-- Every actual spatial difference quotient of a weak linear Poisson solution
is weak harmonic on the genuine overlap of the original and shifted domains. -/
theorem WeakPSourcePair.harmonic_difference_quotient_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (a : Space n) (t : ℝ) :
    WeakPHarmonicPair 2 (Ω∩((fun x => x+a) ⁻¹' Ω))
      (t⁻¹ • ((fun x => u (x+a))-u))
      (t⁻¹ • ((fun x => g (x+a))-g)) := by
  have ho : IsOpen (Ω∩((fun x => x+a) ⁻¹' Ω)) :=
    hu.2.1.inter (hu.2.1.preimage (continuous_id.add continuous_const))
  have hu' := hu.mono_actual inter_subset_left ho
  have hv' := (hu.translate_actual a).mono_actual inter_subset_right ho
  exact (hv'.harmonic_difference_two hu').smul t⁻¹

/-- A local gradient-difference quotient bound derived from the weak PDE.
Together with an L2 translation bound for u, this is the usual W2,2 entry point.
It does not assert the subsequent weak-second-derivative extraction. -/
theorem WeakPSourcePair.gradient_quotient_caccioppoli_two
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (a : Space n) (t : ℝ)
    (hD : LocalDomain D (Ω∩((fun x => x+a) ⁻¹' Ω)))
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1) :
    (∫ x in D,η x^2*‖t⁻¹ • (g (x+a)-g x)‖^2) ≤
      4*∫ x in D,|t⁻¹*(u (x+a)-u x)|^2*‖gradient η x‖^2 := by
  have he := (hu.harmonic_difference_quotient_two a t).caccioppoli_natPow
    (M := 2) hD hη hη0 hη1 (by norm_num) 0
  norm_num only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,sub_zero,Real.rpow_two,Nat.cast_ofNat] at he
  exact he

private theorem difference_pair {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : SobolevPair p D u g) (hv : SobolevPair p D v h) :
    SobolevPair p D (u-v) (g-h) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hu.add (hv.smul (-1))

/-- Local nonlinear flux-defect identity.  Unlike the global zero-boundary
identity, the solutions may have unrelated boundary values: the compact smooth
multiplier constructs the admissible W0 difference test in the proof. -/
theorem WeakPSourcePair.local_flux_difference_identity
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hD : LocalDomain D Ω) {χ : Space n → ℝ} (hχ : SmoothTest D χ) :
    Integrable (fun x => χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))
      (volume.restrict D) ∧
    Integrable (fun x => (u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))
      (volume.restrict D) ∧
    (∫ x in D,χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))=
      -(∫ x in D,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := by
  have su := hu.2.2.1 D hD
  have sv := hv.2.2.1 D hD
  have sd := difference_pair su sv
  let K : Space n → Space n := fun x => χ x • (g x-h x)+(u x-v x) • gradient χ x
  have htest : ZeroBoundarySobolevPair p D (fun x => χ x*(u x-v x)) K :=
    sd.mul_smooth_compactSupport_zeroBoundary hD.1 hχ.1 hχ.2.1 hχ.2.2
  obtain ⟨hgi,hge⟩ := hu.2.2.2 D hD _ _ htest
  obtain ⟨hhi,hhe⟩ := hv.2.2.2 D hD _ _ htest
  haveI := holderConjugate_p_dual hu.1
  have hF := (memLp_pFlux hu.1 su.2.2.1).sub (memLp_pFlux hv.1 sv.2.2.1)
  have hχtop : MemLp χ (∞ : ℝ≥0∞) (volume.restrict D) :=
    hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _
  have hgradtop : MemLp (gradient χ) (∞ : ℝ≥0∞) (volume.restrict D) :=
    (continuous_gradient_of_contDiff_one (hχ.1.of_le (by simp))).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1) _
  have hA : Integrable (fun x => χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))
      (volume.restrict D) := by
    have hx : MemLp (χ • (g-h)) (ENNReal.ofReal p) (volume.restrict D) :=
      sd.2.2.1.smul hχtop
    simpa only [Pi.smul_apply',Pi.sub_apply,inner_smul_right] using
      inner_integrable_of_dual_memLp hF hx
  have hB : Integrable (fun x => (u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))
      (volume.restrict D) := by
    have hx : MemLp ((u-v) • gradient χ) (ENNReal.ofReal p) (volume.restrict D) :=
      hgradtop.smul sd.2.1
    simpa only [Pi.smul_apply',Pi.sub_apply,inner_smul_right] using
      inner_integrable_of_dual_memLp hF hx
  have hsplit : fluxPairing p g K-fluxPairing p h K=
      (fun x => χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))+
      (fun x => (u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := by
    funext x
    simp only [fluxPairing,K,Pi.add_apply,Pi.sub_apply,inner_add_right,
      inner_smul_right,inner_sub_left]
    ring
  have he : (∫ x in D,fluxPairing p g K x-fluxPairing p h K x)=0 := by
    rw [integral_sub hgi hhi,hge,hhe,sub_self]
  change (∫ x in D,(fluxPairing p g K-fluxPairing p h K) x)=0 at he
  rw [hsplit] at he
  change (∫ x in D,
    χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x)+
    (u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))=0 at he
  rw [integral_add hA hB] at he
  exact ⟨hA,hB,by linarith only [he]⟩

/-- For p≥2, the actual local nonlinear weak equation controls a positive
power of the weak-gradient difference by the cutoff error.  Applied to the
translated equation, this is a genuine finite-difference energy estimate. -/
theorem WeakPSourcePair.local_gradient_difference_bound
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hp : 2≤p) (hD : LocalDomain D Ω) {χ : Space n → ℝ}
    (hχ : SmoothTest D χ) (hχ0 : ∀ x,0≤χ x) :
    4*(∫ x in D,χ x*‖(1/2 : ℝ) • (g x-h x)‖^p) ≤
      -p*(∫ x in D,(u x-v x)*
        inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := by
  obtain ⟨hA,_,he⟩ := hu.local_flux_difference_identity hv hD hχ
  have hd := (((hu.2.2.1 D hD).2.2.1).sub
    ((hv.2.2.1 D hD).2.2.1)).const_smul (1/2 : ℝ)
  have hN := integrable_norm_rpow_of_memLp hu.1 hd
  have hχtop : MemLp χ (∞ : ℝ≥0∞) (volume.restrict D) :=
    hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _
  have hI : Integrable (fun x => χ x*‖(1/2 : ℝ) • (g x-h x)‖^p)
      (volume.restrict D) := by
    simpa only [Pi.smul_apply,Pi.sub_apply,Pi.mul_apply] using!
      hN.mul_of_top_right hχtop
  have hle := integral_mono (hI.const_mul 4) (hA.const_mul p) (fun x => by
    have h := mul_le_mul_of_nonneg_left
      (pFlux_pairing_controls_half_difference hp (g x) (h x)) (hχ0 x)
    nlinarith only [h])
  rw [integral_const_mul,integral_const_mul,he] at hle
  simpa only [mul_neg,neg_mul] using hle

/-- Actual singular-range weighted difference energy is finite and controlled
by the weak PDE's cutoff error. No weak Hessian or gradient bound is assumed. -/
theorem WeakPSourcePair.local_weighted_gradient_difference_bound
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hp : p≤2) (hD : LocalDomain D Ω) {χ : Space n → ℝ}
    (hχ : SmoothTest D χ) (hχ0 : ∀ x,0≤χ x) :
    Integrable (fun x => χ x*((p-1)*(‖g x‖+‖h x‖)^(p-2)*‖g x-h x‖^2))
      (volume.restrict D) ∧
    (∫ x in D,χ x*((p-1)*(‖g x‖+‖h x‖)^(p-2)*‖g x-h x‖^2))≤
      -(∫ x in D,(u x-v x)*
        inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := by
  obtain ⟨hA,_,he⟩ := hu.local_flux_difference_identity hv hD hχ
  have hgm := (hu.2.2.1 D hD).2.2.1.1
  have hhm := (hv.2.2.1 D hD).2.2.1.1
  have hweight : AEMeasurable (fun x => (‖g x‖+‖h x‖)^(p-2))
      (volume.restrict D) := (hgm.norm.aemeasurable.add hhm.norm.aemeasurable).pow_const _
  have hnorm : AEMeasurable (fun x => ‖g x-h x‖^2) (volume.restrict D) :=
    (hgm.sub hhm).norm.aemeasurable.pow_const (2 : ℕ)
  have hm : AEStronglyMeasurable
      (fun x => χ x*((p-1)*(‖g x‖+‖h x‖)^(p-2)*‖g x-h x‖^2))
      (volume.restrict D) :=
    (hχ.1.continuous.measurable.aemeasurable.mul
      ((hweight.const_mul (p-1)).mul hnorm)).aestronglyMeasurable
  have hpoint (x : Space n) :
      χ x*((p-1)*(‖g x‖+‖h x‖)^(p-2)*‖g x-h x‖^2)≤
        χ x*inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x) :=
    mul_le_mul_of_nonneg_left
      (pFlux_pairing_controls_weighted_difference hu.1 hp (g x) (h x)) (hχ0 x)
  have hI := hA.mono' hm (Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by
      exact mul_nonneg (hχ0 x) (mul_nonneg
        (mul_nonneg (sub_pos.mpr hu.1).le
          (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _))
        (sq_nonneg _)))]
    exact hpoint x))
  refine ⟨hI,?_⟩
  have hh := integral_mono hI hA hpoint
  rw [he] at hh
  exact hh

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.mono_actual
#print axioms BMCompactPDE.WeakPSourcePair.harmonic_difference_quotient_two
#print axioms BMCompactPDE.WeakPSourcePair.gradient_quotient_caccioppoli_two
#print axioms BMCompactPDE.WeakPSourcePair.local_flux_difference_identity
#print axioms BMCompactPDE.WeakPSourcePair.local_gradient_difference_bound
#print axioms BMCompactPDE.WeakPSourcePair.local_weighted_gradient_difference_bound

end -- exact source's anonymous noncomputable section
end GradientBody_GradientDifference

section GradientBody_GradientReusedTranslation

-- ===== Scratch/CRRelA.lean =====
/-!
# `‖g(· + h) - g‖_p ≤ |h| ‖Dg‖_p` for `C¹` maps on `ℝᵐ`

Pointwise: fundamental theorem of calculus on `τ ↦ g (x + τ h)`; then Jensen on `[0, 1]`,
Tonelli and translation invariance of Lebesgue measure.
-/

/-! Adapted attributed proof: Mazecto, public Prove2Me theorem
67d0148b-a528-4693-828c-f09c3e47e04f, accepted submission
7bc58d37-b255-400f-887c-78f3ef050334. The original exact source and
platform receipt are preserved in scouting/. This is an existing dependency
proof, not new authorship. Imports are actual pinned Mathlib, not theorem
placeholders; helper visibility and namespace were localized. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
namespace BMCompactGradientReuse

open MeasureTheory Set
open scoped ENNReal NNReal

private lemma crra_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ p ≤ ∫⁻ a, f a ^ p ∂μ := by
  rcases hp.eq_or_lt with h | hp
  · subst h; simp
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
    measure_univ, ENNReal.one_rpow, mul_one] at h
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, f a ∂μ) ^ p ≤ ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ a, f a ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private lemma crra_pointwise {g : EuclideanSpace ℝ (Fin m) → F} (hg : ContDiff ℝ 1 g)
    (h x : EuclideanSpace ℝ (Fin m)) :
    ‖g (x + h) - g x‖ₑ ≤
      ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ := by
  have hd : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => g (x + τ • h)) (fderiv ℝ g (x + τ • h) h) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => x + τ • h) h τ := by
      simpa using ((hasDerivAt_id τ).smul_const h).const_add x
    have h2 := (hg.differentiable one_ne_zero (x + τ • h)).hasFDerivAt
    exact h2.comp_hasDerivAt τ h1
  have hcont : Continuous fun τ : ℝ => fderiv ℝ g (x + τ • h) h := by
    have := hg.continuous_fderiv one_ne_zero
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)

theorem classical_translation_norm_bound (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin m) → F) (hg : ContDiff ℝ 1 g) (h : EuclideanSpace ℝ (Fin m)) :
    eLpNorm (fun x => g (x + h) - g x) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ g x‖) p volume := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hpr0 : 0 < p.toReal := by linarith
  set r := p.toReal
  have hcD : Continuous fun x => fderiv ℝ g x := hg.continuous_fderiv one_ne_zero
  haveI : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  -- pointwise bound after Jensen
  have hpt : ∀ x, ‖g (x + h) - g x‖ₑ ^ r ≤
      ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r := by
    intro x
    have hm : AEMeasurable (fun τ : ℝ => ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ((by fun_prop : Continuous fun τ : ℝ => ‖fderiv ℝ g (x + τ • h)‖ₑ).measurable.mul_const
        _).aemeasurable
    calc ‖g (x + h) - g x‖ₑ ^ r
        ≤ (∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ) ^ r :=
          ENNReal.rpow_le_rpow (crra_pointwise hg h x) hpr0.le
      _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, (‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ) ^ r :=
          crra_jensen _ hpr hm
      _ = ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r := by
          rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr0.le enorm_ne_top)]
          congr 1; funext τ
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpr0.le, mul_comm]
  -- Tonelli + translation invariance
  have hswap : ∫⁻ x, ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r =
      ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r := by
    rw [lintegral_lintegral_swap]
    · have : ∀ τ : ℝ, ∫⁻ x, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r = ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r :=
        fun τ => lintegral_add_right_eq_self (fun x => ‖fderiv ℝ g x‖ₑ ^ r) (τ • h)
      simp only [this, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
        Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
    · have : Continuous fun z : EuclideanSpace ℝ (Fin m) × ℝ => ‖fderiv ℝ g (z.1 + z.2 • h)‖ₑ :=
        by fun_prop
      exact (this.measurable.pow_const r).aemeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp',
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  have hnorm : ∀ x, ‖(‖fderiv ℝ g x‖)‖ₑ = ‖fderiv ℝ g x‖ₑ := fun x => by
    rw [← ofReal_norm, ← ofReal_norm, norm_norm]
  simp only [hnorm]
  calc (∫⁻ x, ‖g (x + h) - g x‖ₑ ^ r) ^ (1 / r)
      ≤ (∫⁻ x, ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
    _ = (‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r) ^ (1 / r) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr0.le enorm_ne_top), hswap]
    _ = ENNReal.ofReal ‖h‖ * (∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hpr0.ne', ENNReal.rpow_one, ofReal_norm]

end BMCompactGradientReuse


#print axioms BMCompactGradientReuse.classical_translation_norm_bound

end -- exact source's anonymous noncomputable section
end GradientBody_GradientReusedTranslation

section GradientBody_GradientSobolevTranslation

/-! Actual finite-Lp Sobolev translation estimates.  The classical estimate is
transferred through genuine mollifiers of the raw distributional pair.  No
classical differentiability, representative selection or translation estimate
is assumed for the Sobolev function. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped Topology ENNReal Convolution
namespace BMCompactPDE

theorem SobolevPair.eLpNorm_translation_sub_le
    {n : ℕ} {p : ℝ} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) (a : Space n) :
    eLpNorm (fun x => u (x+a)-u x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖a‖*eLpNorm g (ENNReal.ofReal p) volume := by
  let q := ENNReal.ofReal p
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hu.1.le
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hum : MemLp u q volume := by simpa only [Measure.restrict_univ] using hu.2.1
  have hgm : MemLp g q volume := by simpa only [Measure.restrict_univ] using hu.2.2.1
  let R : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hRp (j : ℕ) : 0<R j := div_pos zero_lt_one (by positivity)
  have hRb (j : ℕ) : R j≤1 := by
    dsimp only [R]
    apply (div_le_iff₀ (by positivity : 0<(j : ℝ)+1)).mpr
    nlinarith only [Nat.cast_nonneg (α := ℝ) j]
  let b : ℕ → ContDiffBump (0 : Space n) := fun j =>
    ⟨R j/2,R j,half_pos (hRp j),half_lt_self (hRp j)⟩
  have hbl : Tendsto (fun j => (b j).rOut) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [b,R,one_div,Function.comp_def] using! tendsto_inv_atTop_zero.comp hn
  let φ : ℕ → Space n → ℝ := fun j => normalizedMollify (b j) u
  have hφ (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ j) :=
    ((b j).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (lsmul ℝ ℝ) (b j).contDiff_normed (hum.locallyIntegrable hq)
  have hφm (j : ℕ) : MemLp (φ j) q volume := memLp_normalizedMollify hq hqt (b j) hum
  have hcomm (j : ℕ) : gradient (φ j)=normalizedMollify (b j) g :=
    hu.gradient_convolution_eq (b j).contDiff_normed (b j).hasCompactSupport_normed
  have hgrad (j : ℕ) : eLpNorm (gradient (φ j)) q volume≤eLpNorm g q volume := by
    rw [hcomm]
    exact eLpNorm_convolution_le_vector hq hqt (b j).continuous_normed
      (b j).hasCompactSupport_normed (b j).nonneg_normed (b j).integral_normed hgm
  have hb (j : ℕ) : eLpNorm (fun x => φ j (x+a)-φ j x) q volume≤
      ENNReal.ofReal ‖a‖*eLpNorm g q volume := by
    have hc := BMCompactGradientReuse.classical_translation_norm_bound q hq hqt
      (φ j) ((hφ j).of_le (by simp)) a
    have hn : (fun x => ‖fderiv ℝ (φ j) x‖)=(fun x => ‖gradient (φ j) x‖) := by
      funext x
      exact ((toDual ℝ (Space n)).symm.norm_map _).symm
    rw [hn,eLpNorm_norm] at hc
    exact hc.trans (mul_le_mul' le_rfl (hgrad j))
  have hlim := tendsto_eLpNorm_mollify_sub_of_memLp hq hqt hbl
    (by norm_num : (0 : ℝ)≤1) hRb hum
  have hbound (j : ℕ) : eLpNorm (fun x => u (x+a)-u x) q volume≤
      eLpNorm (φ j-u) q volume+
        ENNReal.ofReal ‖a‖*eLpNorm g q volume+eLpNorm (φ j-u) q volume := by
    let A := fun x => (u-φ j) (x+a)
    let B := fun x => φ j (x+a)-φ j x
    let C := φ j-u
    have hAm : MemLp A q volume :=
      (hum.sub (hφm j)).comp_measurePreserving (measurePreserving_add_right volume a)
    have hBm : MemLp B q volume :=
      ((hφm j).comp_measurePreserving (measurePreserving_add_right volume a)).sub (hφm j)
    have hCm : MemLp C q volume := (hφm j).sub hum
    have heq : (fun x => u (x+a)-u x)=(A+B)+C := by
      funext x
      simp only [A,B,C,Pi.add_apply,Pi.sub_apply]
      ring
    have hAe : eLpNorm A q volume=eLpNorm (φ j-u) q volume := by
      rw [show eLpNorm A q volume=eLpNorm (u-φ j) q volume from
        eLpNorm_comp_measurePreserving (hum.sub (hφm j)).1
          (measurePreserving_add_right volume a)]
      exact eLpNorm_sub_comm u (φ j) q volume
    rw [heq]
    calc
      eLpNorm (A+B+C) q volume≤eLpNorm (A+B) q volume+eLpNorm C q volume :=
        eLpNorm_add_le (hAm.add hBm).1 hCm.1 hq
      _≤(eLpNorm A q volume+eLpNorm B q volume)+eLpNorm C q volume :=
        add_le_add (eLpNorm_add_le hAm.1 hBm.1 hq) le_rfl
      _≤_ := by
        rw [hAe]
        exact add_le_add (add_le_add le_rfl (hb j)) le_rfl
  have ht := (hlim.add (tendsto_const_nhds
    (x := ENNReal.ofReal ‖a‖*eLpNorm g q volume))).add hlim
  simp only [zero_add,add_zero] at ht
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

theorem SobolevPair.eLpNorm_difference_quotient_le
    {n : ℕ} {p : ℝ} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) (v : Space n) {t : ℝ} (ht : t≠0) :
    eLpNorm (t⁻¹ • (fun x => u (x+t • v)-u x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ‖v‖*eLpNorm g (ENNReal.ofReal p) volume := by
  rw [eLpNorm_const_smul]
  have hb := mul_le_mul' (le_refl ‖t⁻¹‖ₑ) (hu.eLpNorm_translation_sub_le (t • v))
  have he : ‖t⁻¹‖ₑ*ENNReal.ofReal ‖t • v‖=ENNReal.ofReal ‖v‖ := by
    rw [← ofReal_norm,← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    rw [norm_smul,norm_inv,← mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht),one_mul]
  simpa only [← mul_assoc,he] using hb

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.eLpNorm_translation_sub_le
#print axioms BMCompactPDE.SobolevPair.eLpNorm_difference_quotient_le

end -- exact source's anonymous noncomputable section
end GradientBody_GradientSobolevTranslation

section GradientBody_GradientRegularizedFlux

/-! Genuine smooth regularization of the p-Laplace flux. These are properties
of the explicit operator, not smoothness premises on a weak PDE solution. They
are reference-equation ingredients for the approximation step in gradient
regularity; no regularized solution is assumed or constructed in this file. -/
noncomputable section
set_option autoImplicit false
open Set InnerProductSpace
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_regularized_pFlux (p : ℝ) {ε : ℝ} (hε : ε≠0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => (ε^2+‖v‖^2)^((p-2)/2) • v) := by
  have hs : ∀ v : E, ε^2+‖v‖^2≠0 := fun v =>
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)).ne'
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne hs).smul contDiff_id

theorem hasFDerivAt_regularized_pFlux (p : ℝ) {ε : ℝ} (hε : ε≠0) (v : E) :
    HasFDerivAt (fun w : E => (ε^2+‖w‖^2)^((p-2)/2) • w)
      ((ε^2+‖v‖^2)^((p-2)/2) • ContinuousLinearMap.id ℝ E+
        (((p-2)*(ε^2+‖v‖^2)^((p-4)/2)) • innerSL ℝ v).smulRight v) v := by
  have hpos : 0<ε^2+‖v‖^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)
  have hs := (hasFDerivAt_id v).norm_sq.const_add (ε^2)
  have hr := hs.rpow_const (p := (p-2)/2) (Or.inl hpos.ne')
  have hd := hr.smul (hasFDerivAt_id v)
  convert! hd using 1
  ext h
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,coe_innerSL_apply,smul_eq_mul,id_eq]
  rw [show (p-2)/2-1=(p-4)/2 by ring]
  module

omit [InnerProductSpace ℝ E] in
private theorem regularized_power_shift (p : ℝ) {ε : ℝ} (hε : ε≠0) (v : E) :
    (ε^2+‖v‖^2)^((p-4)/2)*(ε^2+‖v‖^2)=(ε^2+‖v‖^2)^((p-2)/2) := by
  have hpos : 0<ε^2+‖v‖^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)
  rw [← Real.rpow_add_one hpos.ne']
  congr 1
  ring

theorem regularized_pFlux_jacobian_quadratic_lower
    (p : ℝ) {ε : ℝ} (hε : ε≠0) (v h : E) :
    min 1 (p-1)*(ε^2+‖v‖^2)^((p-2)/2)*‖h‖^2≤
      inner ℝ (fderiv ℝ (fun w : E => (ε^2+‖w‖^2)^((p-2)/2) • w) v h) h := by
  rw [(hasFDerivAt_regularized_pFlux p hε v).fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
    coe_innerSL_apply,inner_add_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,smul_eq_mul]
  have hpow := regularized_power_shift p hε v
  have hweight : 0≤(ε^2+‖v‖^2)^((p-4)/2) :=
    Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have hin : (inner ℝ v h)^2≤‖v‖^2*‖h‖^2 := by
    have hh := abs_real_inner_le_norm v h
    simpa only [sq_abs,mul_pow] using
      (sq_le_sq₀ (abs_nonneg (inner ℝ v h))
        (mul_nonneg (norm_nonneg v) (norm_nonneg h))).mpr hh
  have hib : (inner ℝ v h)^2≤(ε^2+‖v‖^2)*‖h‖^2 :=
    hin.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg ε)) (sq_nonneg _))
  rcases le_total 2 p with hge|hle
  · rw [min_eq_left (by linarith : (1 : ℝ)≤p-1)]
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hge) hweight)
      (sq_nonneg (inner ℝ v h))
    nlinarith only [hh]
  · rw [min_eq_right (by linarith : p-1≤(1 : ℝ))]
    have hh := mul_le_mul_of_nonpos_left hib
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hweight)
    have he := congrArg (fun z : ℝ => (p-2)*z*‖h‖^2) hpow
    nlinarith only [hh,he]

theorem regularized_pFlux_jacobian_strict_positive
    {p : ℝ} (hp : 1<p) {ε : ℝ} (hε : ε≠0) (v : E) {h : E} (hh : h≠0) :
    0 < inner ℝ
      (fderiv ℝ (fun w : E => (ε^2+‖w‖^2)^((p-2)/2) • w) v h) h := by
  have hmin : 0<min (1 : ℝ) (p-1) := lt_min zero_lt_one (sub_pos.mpr hp)
  have hpos : 0<ε^2+‖v‖^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)
  exact (mul_pos (mul_pos hmin (Real.rpow_pos_of_pos hpos _))
    (pow_pos (norm_pos_iff.mpr hh) 2)).trans_le
      (regularized_pFlux_jacobian_quadratic_lower p hε v h)

end BMCompactPDE
#print axioms BMCompactPDE.contDiff_regularized_pFlux
#print axioms BMCompactPDE.hasFDerivAt_regularized_pFlux
#print axioms BMCompactPDE.regularized_pFlux_jacobian_quadratic_lower
#print axioms BMCompactPDE.regularized_pFlux_jacobian_strict_positive

end -- exact source's anonymous noncomputable section
end GradientBody_GradientRegularizedFlux
