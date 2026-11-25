import UpstreamMorreyLocal
import PotentialSobolevBoost

/-! A genuine quantitative local Sobolev coefficient selected before the
raw scalar and its independently supplied weak gradient. Compact localization
and the actual W0 Sobolev inequality give both higher integrability and its
norm bound; no higher norm or desired inequality is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_local_sobolev_norm_coefficient
    {n : ℕ} {r : ℝ} (hr : 1<r) (hrn : r<(n : ℝ))
    {U D : Set (Space n)} (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ (u : Space n → ℝ) (g : Space n → Space n),SobolevPair r U u g →
      MemLp u (ENNReal.ofReal ((n : ℝ)*r/((n : ℝ)-r))) (volume.restrict D) ∧
      (eLpNorm u (ENNReal.ofReal ((n : ℝ)*r/((n : ℝ)-r))) (volume.restrict D)).toReal≤
        C*((eLpNorm u (ENNReal.ofReal r) (volume.restrict U)).toReal+
          (eLpNorm g (ENNReal.ofReal r) (volume.restrict U)).toReal) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU hD.2.2
  let χ : Space n → ℝ := fun x=>Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hs : tsupport χ⊆U :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0≤χ x := Real.smoothTransition.nonneg _
  have hχle (x : Space n) : χ x≤1 := Real.smoothTransition.le_one _
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x (subset_closure hx))
  have hgc : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hc).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient χ x‖≤P := hPb _ (mem_range_self x)
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) r
  refine ⟨(S : ℝ)*(1+P),mul_nonneg S.coe_nonneg (by positivity),?_⟩
  intro u g hu
  let q : ℝ≥0∞ := ENNReal.ofReal r
  let t : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ)*r/((n : ℝ)-r))
  let μ := volume.restrict U
  let F : Space n → ℝ := fun x=>χ x*u x
  let A : Space n → Space n := fun x=>χ x • g x
  let B : Space n → Space n := fun x=>u x • gradient χ x
  let H : Space n → Space n := fun x=>A x+B x
  have hw : ZeroBoundarySobolevPair r U F H := hu.mul_smooth_compactSupport_zeroBoundary hU hχ hc hs
  have hboost := hw.critical_sobolev_explicit hrn
  have hAb (x : Space n) : ‖A x‖≤‖g x‖ := by
    change ‖χ x • g x‖≤‖g x‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hχ0 x)]
    exact (mul_le_mul_of_nonneg_right (hχle x) (norm_nonneg _)).trans_eq (one_mul _)
  have hBb (x : Space n) : ‖B x‖≤P*‖u x‖ := by
    change ‖u x • gradient χ x‖≤P*‖u x‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hPx x) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hA : MemLp A q μ := hu.2.2.1.of_le
    (hχ.continuous.aestronglyMeasurable.smul hu.2.2.1.1) (Eventually.of_forall hAb)
  have hB : MemLp B q μ := hu.2.1.of_le_mul
    (hu.2.1.1.smul hgc.aestronglyMeasurable) (Eventually.of_forall hBb)
  have hAN : eLpNorm A q μ≤eLpNorm g q μ := eLpNorm_mono_ae (Eventually.of_forall hAb)
  have hBN : eLpNorm B q μ≤ENNReal.ofReal P*eLpNorm u q μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hBb) q
  have hsum : eLpNorm H q μ≤eLpNorm g q μ+ENNReal.ofReal P*eLpNorm u q μ :=
    (eLpNorm_add_le hA.1 hB.1 (ENNReal.one_le_ofReal.mpr hr.le)).trans (add_le_add hAN hBN)
  have hgf : eLpNorm g q μ≠(∞ : ℝ≥0∞) := hu.2.2.1.eLpNorm_ne_top
  have huf : eLpNorm u q μ≠(∞ : ℝ≥0∞) := hu.2.1.eLpNorm_ne_top
  have hpf : ENNReal.ofReal P*eLpNorm u q μ≠(∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top huf
  have hnorm : (eLpNorm H q μ).toReal≤(eLpNorm g q μ).toReal+P*(eLpNorm u q μ).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hgf,hpf⟩) hsum
    simpa only [ENNReal.toReal_add hgf hpf,ENNReal.toReal_mul,ENNReal.toReal_ofReal hP.le] using hh
  have hnorm' : (eLpNorm H q μ).toReal≤(1+P)*((eLpNorm u q μ).toReal+(eLpNorm g q μ).toReal) := by
    nlinarith only [hnorm,ENNReal.toReal_nonneg (a:=eLpNorm u q μ),
      mul_nonneg hP.le (ENNReal.toReal_nonneg (a:=eLpNorm g q μ))]
  have hDU : D⊆U := subset_closure.trans hD.2.2
  have hFu : F=ᵐ[volume.restrict D] u := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    simp only [F,hχ1 x hx,one_mul]
  have hmem : MemLp u t (volume.restrict D) :=
    (memLp_congr_ae hFu).mp (hboost.1.mono_measure (Measure.restrict_mono hDU le_rfl))
  have hbound : eLpNorm u t (volume.restrict D)≤(S : ℝ≥0∞)*eLpNorm H q μ := by
    calc
      _=eLpNorm F t (volume.restrict D) := (eLpNorm_congr_ae hFu).symm
      _≤eLpNorm F t μ := eLpNorm_mono_measure _ (Measure.restrict_mono hDU le_rfl)
      _≤_ := hboost.2
  have hreal : (eLpNorm u t (volume.restrict D)).toReal≤(S : ℝ)*(eLpNorm H q μ).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hw.1.2.2.1.eLpNorm_ne_top) hbound
    simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal] using hh
  refine ⟨hmem,?_⟩
  calc
    _≤(S : ℝ)*(eLpNorm H q μ).toReal := hreal
    _≤(S : ℝ)*((1+P)*((eLpNorm u q μ).toReal+(eLpNorm g q μ).toReal)) :=
      mul_le_mul_of_nonneg_left hnorm' S.coe_nonneg
    _=_ := by ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_sobolev_norm_coefficient
