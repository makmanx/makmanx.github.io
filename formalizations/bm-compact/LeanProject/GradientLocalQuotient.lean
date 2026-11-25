import GradientAnalyticBatch
import Mathlib.Topology.MetricSpace.Thickening

/-! Construct local translation models and quotient bounds for actual raw
Sobolev pairs. The whole-space model is selected by genuine compact smooth
localization; no extension, differentiability or quotient estimate is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

theorem SobolevPair.exists_compact_translation_model {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ δ : ℝ,0<δ ∧ ∃ U : Space n → ℝ,∃ G : Space n → Space n,
      SobolevPair p univ U G ∧ EqOn U u (cthickening δ K) := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK.cthickening hΩ hδΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp hf.1
  have hχ0 : χ 0=Real.smoothTransition (f 0) := rfl
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ1 (x : Space n) (hx : x∈cthickening δ K) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  refine ⟨δ,hδ,fun x => χ x*u x,fun x => χ x • g x+u x • gradient χ x,
    hu.mul_smooth_compactSupport_global hΩ hχ hχc hχs,?_⟩
  intro x hx
  change χ x*u x=u x
  rw [hχ1 x hx,one_mul]

theorem SobolevPair.exists_local_difference_quotient_bound {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ a : Space n,a≠0 → ‖a‖≤δ →
      eLpNorm (fun x => ‖a‖⁻¹*(u (x+a)-u x)) (ENNReal.ofReal p)
        (volume.restrict K)≤ENNReal.ofReal C := by
  obtain ⟨δ,hδ,U,G,hS,hmodel⟩ := hu.exists_compact_translation_model hΩ hK hKΩ
  have hG : MemLp G (ENNReal.ofReal p) volume := by
    simpa only [Measure.restrict_univ] using hS.2.2.1
  let C := (eLpNorm G (ENNReal.ofReal p) volume).toReal
  refine ⟨δ,C,hδ,ENNReal.toReal_nonneg,?_⟩
  intro a ha haδ
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  have hapos : 0<‖a‖ := norm_pos_iff.mpr ha
  have hdir : ‖‖a‖⁻¹ • a‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hapos),inv_mul_cancel₀ hn]
  have hstep : ‖a‖ • (‖a‖⁻¹ • a)=a := by
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hbound : eLpNorm (fun x => ‖a‖⁻¹*(U (x+a)-U x)) (ENNReal.ofReal p) volume≤
      eLpNorm G (ENNReal.ofReal p) volume := by
    have hh := hS.eLpNorm_difference_quotient_le (‖a‖⁻¹ • a) (t := ‖a‖) hn
    simpa only [hdir,hstep,Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_one,one_mul] using! hh
  have heq : (fun x => ‖a‖⁻¹*(u (x+a)-u x))=ᵐ[volume.restrict K]
      (fun x => ‖a‖⁻¹*(U (x+a)-U x)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hx0 : x∈cthickening δ K := mem_cthickening_of_dist_le x x δ K hx
      (by simpa only [dist_self] using hδ.le)
    have hxa : x+a∈cthickening δ K := mem_cthickening_of_dist_le (x+a) x δ K hx
      (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδ)
    rw [hmodel hx0,hmodel hxa]
  rw [eLpNorm_congr_ae heq]
  calc
    _≤eLpNorm (fun x => ‖a‖⁻¹*(U (x+a)-U x)) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _≤eLpNorm G (ENNReal.ofReal p) volume := hbound
    _=ENNReal.ofReal C := (ENNReal.ofReal_toReal hG.eLpNorm_ne_top).symm

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.exists_compact_translation_model
#print axioms BMCompactPDE.SobolevPair.exists_local_difference_quotient_bound
