import PotentialDeGiorgiStep

/-! A genuine superlinear one-step level-set recurrence for bounded actual weak
subsolutions. The only extra data are ordinary upper/cutoff bounds and inner
cutoff equality. No iteration, Harnack or selected regular representative is
assumed. Further iteration and quantitative nested cutoffs remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

theorem WeakPSubsolutionPair.bounded_superlevel_step
    {n M : ℕ} {p k h U L : ℝ} {Ω D K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hηK : ∀ x∈K, η x=1) (hgrad : ∀ x∈D, ‖gradient η x‖≤L)
    (hL : 0≤L) (hub : ∀ x∈D, u x≤U) (hkU : k≤U)
    (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (hkh : k<h) :
    1<((n : ℝ)*p/((n : ℝ)-p))/p ∧
    (ENNReal.ofReal (h-k)) ^ ((n : ℝ)*p/((n : ℝ)-p)) *
        (volume.restrict D) (K ∩ {x | h≤u x}) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
        ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p)) *
          (((U-k)^p*L^p) * ((volume.restrict D) {x | k<u x}).toReal)) ^ p⁻¹)) ^
        ((n : ℝ)*p/((n : ℝ)-p)) := by
  let μ := volume.restrict D
  let A : Set (Space n) := {x | k<u x}
  let T : ℝ := (U-k)^p*L^p
  let B : Space n → ℝ := fun x => (max (u x-k) 0)^p*‖gradient η x‖^p
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hd : 0<(n : ℝ)-p := sub_pos.mpr hpn
  have hQ0 : 0<Q := div_pos (mul_pos hn0 hp0) hd
  have hQp : 1<Q/p := by
    have he : Q/p=(n : ℝ)/((n : ℝ)-p) := by
      dsimp only [Q]
      field_simp [hp0.ne',hd.ne']
    rw [he]
    exact (one_lt_div hd).mpr (by linarith)
  refine ⟨hQp,?_⟩
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hs := hu.2.2.1 D hD
  have hA : NullMeasurableSet A μ :=
    nullMeasurableSet_lt aemeasurable_const hs.2.1.1.aemeasurable
  have hTI : Integrable (A.indicator (fun _ => T)) μ :=
    (integrable_const T).indicator₀ hA
  have hz : AEStronglyMeasurable (fun x => max (u x-k) 0) μ := by
    exact ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable hs.2.1.1
  have hrpow : Continuous (fun a : ℝ => a^p) :=
    continuous_id.rpow_const (fun _ => Or.inr hp0.le)
  have hgpow : Continuous (fun x => ‖gradient η x‖^p) :=
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1).norm.rpow_const
      (fun _ => Or.inr hp0.le)
  have hBm : AEStronglyMeasurable B μ :=
    (hrpow.comp_aestronglyMeasurable hz).mul hgpow.aestronglyMeasurable
  have hB0 (x : Space n) : 0≤B x := mul_nonneg
    (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hle : B≤ᵐ[μ] A.indicator (fun _ => T) := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hxD
    by_cases hx : k<u x
    · rw [indicator_of_mem (show x∈A from hx)]
      change (max (u x-k) 0)^p*‖gradient η x‖^p≤(U-k)^p*L^p
      rw [max_eq_left (sub_pos.mpr hx).le]
      exact mul_le_mul
        (Real.rpow_le_rpow (sub_pos.mpr hx).le (sub_le_sub_right (hub x hxD) k) hp0.le)
        (Real.rpow_le_rpow (norm_nonneg _) (hgrad x hxD) hp0.le)
        (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (sub_nonneg.mpr hkU) _)
    · rw [indicator_of_notMem (show x∉A from hx)]
      simp only [B,max_eq_right (sub_nonpos.mpr (le_of_not_gt hx)),Real.zero_rpow hp0.ne',zero_mul]
      exact le_rfl
  have hBI : Integrable B μ := hTI.mono_nonneg hBm
    (Eventually.of_forall hB0) hle
  have hi := integral_mono_ae hBI hTI hle
  rw [integral_indicator₀ hA,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hi
  have hI : (∫ x, B x ∂μ)≤T*(μ A).toReal := by
    simpa only [mul_comm] using hi
  have hE : 0≤E := by dsimp only [E]; positivity
  have hbase : (E*(∫ x, B x ∂μ))^p⁻¹ ≤ (E*(T*(μ A).toReal))^p⁻¹ :=
    Real.rpow_le_rpow (mul_nonneg hE (integral_nonneg hB0))
      (mul_le_mul_of_nonneg_left hI hE) (inv_nonneg.mpr hp0.le)
  have hstep := hu.superlevel_step hD hη hη0 hη1 hηK hm hpn hkh
  apply hstep.trans
  apply ENNReal.rpow_le_rpow _ hQ0.le
  exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hbase) bot_le

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.bounded_superlevel_step
