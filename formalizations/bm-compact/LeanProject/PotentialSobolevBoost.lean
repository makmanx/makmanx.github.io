import BMCompactCriticalChecked
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Actual critical Sobolev gain for the concrete W0 graph. Smooth GNS is
transferred using the genuinely constructed graph approximants and lower
semicontinuity under convergence in measure. It is applicable in the requested
subcritical regime 1<p<n, not the unrelated p>n Morrey regime. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

/-- A proved smooth norm estimate passes to the actual W0 graph. The later
critical Sobolev theorem supplies the estimate from Mathlib's actual GNS. -/
theorem ZeroBoundarySobolevPair.eLpNorm_le_of_smooth_bound
    {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) {q : ℝ≥0∞} (C : ℝ≥0)
    (hbound : ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ q (volume.restrict D) ≤
        C * eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D)) :
    eLpNorm u q (volume.restrict D) ≤
      C * eLpNorm g (ENNReal.ofReal p) (volume.restrict D) := by
  obtain ⟨hS,φ,hφ,hLu,hLg⟩ := hu
  let μ := volume.restrict D
  let P := ENNReal.ofReal p
  have hp0 : 0<p := zero_lt_one.trans hS.1
  have hP0 : P≠0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hP : 1≤P := ENNReal.one_le_ofReal.mpr hS.1.le
  have hφS (j : ℕ) := (hφ j).sobolevPair hS.1
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm hP0
    (fun j => (hφS j).2.1.1) hS.2.1.1 hLu
  let ε : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (((j : ℝ)+1)⁻¹)
  have hεp (j : ℕ) : 0<ε j := ENNReal.ofReal_pos.mpr (inv_pos.mpr (by positivity))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [ε,Function.comp_def,ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hn)
  have hb (j : ℕ) : eLpNorm u q μ ≤ C*(ε j+eLpNorm g P μ) := by
    have hsmall := hLg.eventually (eventually_lt_nhds (hεp j))
    apply eLpNorm_le_of_tendstoInMeasure _ hmeas (fun k => (hφS k).2.1.1)
    filter_upwards [hsmall] with k hk
    have ht := eLpNorm_add_le ((hφS k).2.2.1.1.sub hS.2.2.1.1) hS.2.2.1.1 hP
    rw [sub_add_cancel (gradient (φ k)) g] at ht
    exact (hbound (φ k) (hφ k)).trans
      (mul_le_mul_of_nonneg_left (ht.trans (add_le_add hk.le le_rfl))
        (show 0≤(C : ℝ≥0∞) from bot_le))
  have hright : Tendsto (fun j => (C : ℝ≥0∞)*(ε j+eLpNorm g P μ)) atTop
      (𝓝 ((C : ℝ≥0∞)*eLpNorm g P μ)) := by
    simpa only [zero_add] using ENNReal.Tendsto.const_mul
      (hεlim.add_const (eLpNorm g P μ)) (Or.inr ENNReal.coe_ne_top)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hright (Eventually.of_forall hb)

/-- Genuine critical Sobolev gain for arbitrary actual W0 pairs, at the uniquely
determined exponent q with 1/q=1/p-1/n. No smoothness of u is assumed. -/
theorem ZeroBoundarySobolevPair.critical_sobolev
    {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hpn : p<(n : ℝ))
    {q : ℝ≥0} (hq : (q : ℝ)⁻¹=p⁻¹-(n : ℝ)⁻¹) :
    MemLp u (q : ℝ≥0∞) (volume.restrict D) ∧
    eLpNorm u (q : ℝ≥0∞) (volume.restrict D) ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
        eLpNorm g (ENNReal.ofReal p) (volume.restrict D) := by
  have hp0 : 0<p := zero_lt_one.trans hu.1.1
  let P : ℝ≥0 := .mk p hp0.le
  have hPe : (P : ℝ≥0∞)=ENNReal.ofReal p := by
    exact (ENNReal.ofReal_eq_coe_nnreal hp0.le).symm
  have hP : 1≤P := by exact_mod_cast hu.1.1.le
  have hn0 : 0<n := by exact_mod_cast (hp0.trans hpn)
  have hdim : 0<Module.finrank ℝ (Space n) := by
    simpa only [Space,finrank_euclideanSpace,Fintype.card_fin] using hn0
  have hq' : (q : ℝ)⁻¹=(P : ℝ)⁻¹-(Module.finrank ℝ (Space n) : ℝ)⁻¹ := by
    simpa only [P,NNReal.coe_mk,Space,finrank_euclideanSpace,Fintype.card_fin] using hq
  have hsmooth : ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ (q : ℝ≥0∞) (volume.restrict D) ≤
        eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
          eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D) := by
    intro φ hφ
    have hi := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure (Space n))
      (hφ.1.of_le (by simp) : ContDiff ℝ 1 φ) hφ.2.1 hP hdim hq'
    have hnorm : eLpNorm (fderiv ℝ φ) (P : ℝ≥0∞) (volume : Measure (Space n)) =
        eLpNorm (gradient φ) (P : ℝ≥0∞) volume := by
      apply eLpNorm_congr_norm_ae
      exact Eventually.of_forall (fun x => by
        simpa only [gradient] using
          ((InnerProductSpace.toDual ℝ (Space n)).symm.norm_map (fderiv ℝ φ x)).symm)
    rw [hnorm,hPe] at hi
    have hsupport : Function.support φ⊆D := (subset_tsupport φ).trans hφ.2.2
    have hgsupport : Function.support (gradient φ)⊆D := by
      intro x hx
      by_contra hxD
      exact hx (BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
        (fun ht => hxD (hφ.2.2 ht)))
    simpa only [P,NNReal.coe_mk,eLpNorm_restrict_eq_of_support_subset hsupport,
      eLpNorm_restrict_eq_of_support_subset hgsupport] using hi
  have hb := hu.eLpNorm_le_of_smooth_bound
    (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p) hsmooth
  refine ⟨⟨hu.1.2.1.1,?_⟩,hb⟩
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.1.2.2.1.2)

/-- Explicit n*p/(n-p) version of the preceding critical-exponent theorem. -/
theorem ZeroBoundarySobolevPair.critical_sobolev_explicit
    {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hpn : p<(n : ℝ)) :
    MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) (volume.restrict D) ∧
    eLpNorm u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) (volume.restrict D) ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
        eLpNorm g (ENNReal.ofReal p) (volume.restrict D) := by
  have hp0 : 0<p := zero_lt_one.trans hu.1.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hd : 0<(n : ℝ)-p := sub_pos.mpr hpn
  let q : ℝ≥0 := .mk ((n : ℝ)*p/((n : ℝ)-p)) (div_nonneg (mul_nonneg hn0.le hp0.le) hd.le)
  have hq : (q : ℝ)⁻¹=p⁻¹-(n : ℝ)⁻¹ := by
    simp only [q,NNReal.coe_mk]
    field_simp [ne_of_gt hp0,ne_of_gt hn0,ne_of_gt hd]
    <;> ring
  have hqe : (q : ℝ≥0∞)=ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p)) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (div_nonneg (mul_nonneg hn0.le hp0.le) hd.le)).symm
  simpa only [hqe] using hu.critical_sobolev hpn hq

end BMCompactPDE
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.eLpNorm_le_of_smooth_bound
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.critical_sobolev
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.critical_sobolev_explicit
