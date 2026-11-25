import GradientLocalQuotient

/-! A single compact cutoff gives a quotient coefficient chosen BEFORE the
actual Sobolev function/gradient. The bound depends linearly on their actual
Lp norms. This is the quantitative localization required for uniform families;
no desired quotient bound, classical derivative or gradient ceiling is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem SobolevPair.exists_uniform_local_difference_quotient_coefficient
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧
      ∀ (u : Space n → ℝ) (g : Space n → Space n),SobolevPair p Ω u g →
        ∀ a : Space n,a≠0 → ‖a‖≤δ →
          eLpNorm (fun x => ‖a‖⁻¹*(u (x+a)-u x)) (ENNReal.ofReal p)
            (volume.restrict K)≤ENNReal.ofReal (C*
              ((eLpNorm u (ENNReal.ofReal p) (volume.restrict Ω)).toReal+
               (eLpNorm g (ENNReal.ofReal p) (volume.restrict Ω)).toReal)) := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK.cthickening hΩ hδΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0≤χ x := Real.smoothTransition.nonneg _
  have hχle (x : Space n) : χ x≤1 := Real.smoothTransition.le_one _
  have hχ1 (x : Space n) (hx : x∈cthickening δ K) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hgc : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hχc).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient χ x‖≤P := hPb _ (mem_range_self x)
  refine ⟨δ,1+P,hδ,by positivity,?_⟩
  intro u g hu a ha haδ
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let μ := volume.restrict Ω
  let U : Space n → ℝ := fun x => χ x*u x
  let A : Space n → Space n := fun x => χ x • g x
  let B : Space n → Space n := fun x => u x • gradient χ x
  let G : Space n → Space n := fun x => A x+B x
  have hS : SobolevPair p univ U G := hu.mul_smooth_compactSupport_global hΩ hχ hχc hχs
  have hG : MemLp G q volume := by simpa only [Measure.restrict_univ] using hS.2.2.1
  have hAbound (x : Space n) : ‖A x‖≤‖g x‖ := by
    change ‖χ x • g x‖≤‖g x‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hχ0 x)]
    exact (mul_le_mul_of_nonneg_right (hχle x) (norm_nonneg _)).trans_eq (one_mul _)
  have hBbound (x : Space n) : ‖B x‖≤P*‖u x‖ := by
    change ‖u x • gradient χ x‖≤P*‖u x‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hPx x) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hA : MemLp A q μ := hu.2.2.1.of_le
    (hχ.continuous.aestronglyMeasurable.smul hu.2.2.1.1) (Eventually.of_forall hAbound)
  have hB : MemLp B q μ := hu.2.1.of_le_mul
    (hu.2.1.1.smul hgc.aestronglyMeasurable) (Eventually.of_forall hBbound)
  have hGzero (x : Space n) (hx : x∉Ω) : G x=0 := by
    have hxt : x∉tsupport χ := fun ht => hx (hχs ht)
    have hχx := image_eq_zero_of_notMem_tsupport hxt
    have hgχ := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hxt
    simp only [G,A,B,hχx,hgχ,zero_smul,smul_zero,add_zero]
  have hGi : Ω.indicator G=G := by
    funext x
    by_cases hx : x∈Ω
    · exact indicator_of_mem hx G
    · simp only [indicator_of_notMem hx,hGzero x hx]
  have hGN : eLpNorm G q volume=eLpNorm G q μ := by
    calc
      _=eLpNorm (Ω.indicator G) q volume := by rw [hGi]
      _=_ := eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet
  have hAN : eLpNorm A q μ≤eLpNorm g q μ := eLpNorm_mono_ae (Eventually.of_forall hAbound)
  have hBN : eLpNorm B q μ≤ENNReal.ofReal P*eLpNorm u q μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hBbound) q
  have hsum : eLpNorm G q μ≤eLpNorm g q μ+ENNReal.ofReal P*eLpNorm u q μ :=
    (eLpNorm_add_le hA.1 hB.1 (ENNReal.one_le_ofReal.mpr hp.le)).trans (add_le_add hAN hBN)
  have hgfinite : eLpNorm g q μ≠(∞ : ℝ≥0∞) := hu.2.2.1.eLpNorm_ne_top
  have hufinite : eLpNorm u q μ≠(∞ : ℝ≥0∞) := hu.2.1.eLpNorm_ne_top
  have hprod : ENNReal.ofReal P*eLpNorm u q μ≠(∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hufinite
  have hnorm : (eLpNorm G q volume).toReal≤
      (eLpNorm g q μ).toReal+P*(eLpNorm u q μ).toReal := by
    rw [hGN]
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hgfinite,hprod⟩) hsum
    simpa only [ENNReal.toReal_add hgfinite hprod,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hP.le] using hh
  have hnorm' : (eLpNorm G q volume).toReal≤(1+P)*
      ((eLpNorm u q μ).toReal+(eLpNorm g q μ).toReal) := by
    have hU0 : 0≤(eLpNorm u q μ).toReal := ENNReal.toReal_nonneg
    have hG0 : 0≤(eLpNorm g q μ).toReal := ENNReal.toReal_nonneg
    nlinarith only [hnorm,hU0,mul_nonneg hP.le hG0]
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  have hapos : 0<‖a‖ := norm_pos_iff.mpr ha
  have hdir : ‖‖a‖⁻¹ • a‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hapos),inv_mul_cancel₀ hn]
  have hstep : ‖a‖ • (‖a‖⁻¹ • a)=a := by
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hbound : eLpNorm (fun x => ‖a‖⁻¹*(U (x+a)-U x)) q volume≤eLpNorm G q volume := by
    have hh := hS.eLpNorm_difference_quotient_le (‖a‖⁻¹ • a) (t := ‖a‖) hn
    simpa only [hdir,hstep,Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_one,one_mul] using! hh
  have heq : (fun x => ‖a‖⁻¹*(u (x+a)-u x))=ᵐ[volume.restrict K]
      (fun x => ‖a‖⁻¹*(U (x+a)-U x)) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hx0 : x∈cthickening δ K := mem_cthickening_of_dist_le x x δ K hx
      (by simpa only [dist_self] using hδ.le)
    have hxa : x+a∈cthickening δ K := mem_cthickening_of_dist_le (x+a) x δ K hx
      (by simpa only [dist_eq_norm,add_sub_cancel_left] using haδ)
    have hUx : U x=u x := by change χ x*u x=u x;rw [hχ1 x hx0,one_mul]
    have hUxa : U (x+a)=u (x+a) := by change χ (x+a)*u (x+a)=u (x+a);rw [hχ1 (x+a) hxa,one_mul]
    rw [hUx,hUxa]
  rw [eLpNorm_congr_ae heq]
  calc
    _≤eLpNorm (fun x => ‖a‖⁻¹*(U (x+a)-U x)) q volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _≤eLpNorm G q volume := hbound
    _=ENNReal.ofReal (eLpNorm G q volume).toReal := (ENNReal.ofReal_toReal hG.eLpNorm_ne_top).symm
    _≤_ := ENNReal.ofReal_le_ofReal hnorm'

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.exists_uniform_local_difference_quotient_coefficient
