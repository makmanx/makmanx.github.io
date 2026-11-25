import CriticalGreenAnnularEnergy

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem critical_flux_young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (hn : 2 ≤ n) (v w : E) :
    ‖pFlux n v‖*‖w‖ ≤ ‖v‖^n + ‖w‖^n := by
  have hp : 1 < (n : ℝ) := by exact_mod_cast (show 1<n by omega)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  rw [norm_pFlux hp]
  simp only [Nat.cast_succ,add_sub_cancel_right,Real.rpow_natCast,pow_succ]
  rcases le_total ‖w‖ ‖v‖ with h|h
  · exact (mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg _) _)).trans
      (le_add_of_nonneg_right (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
  · exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h _) (norm_nonneg _)).trans
      (le_add_of_nonneg_left (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))

/-- A scale-free estimate for the absolute error of one cutoff transition.
The integral is over the whole window. Only the two gradient energies in the
transition shell and the cutoff's own n-energy contribute. -/
theorem critical_shell_flux_error_bound
    {n : ℕ} (hn : 2≤n) {W V : Set (Space n)} (hW : IsOpen W) (hWV : W⊆V) (hV : MeasurableSet V)
    {u v : Space n → ℝ} {g h : Space n → Space n} (su : SobolevPair (n:ℝ) W u g)
    (sv : SobolevPair (n:ℝ) W v h) {A : ℝ} (hA : 0≤A) (hgap : ∀ x∈W,|u x-v x|≤A)
    {η : Space n → ℝ} (hc : Continuous (gradient η)) (hoff : ∀ x, x∉W → gradient η x=0)
    (hI : Integrable (fun x=>‖gradient η x‖^n) volume) :
    IntegrableOn (fun x => |(u x-v x)*inner ℝ (pFlux n (g x)-pFlux n (h x)) (gradient η x)|) V volume ∧
    (∫ x in V, |(u x-v x)*inner ℝ (pFlux n (g x)-pFlux n (h x)) (gradient η x)|) ≤
    A*((∫ x in W, ‖g x‖^n)+(∫ x in W, ‖h x‖^n)+2*∫ x, ‖gradient η x‖^n ∂volume) := by
  let J := fun x => |(u x-v x)*inner ℝ (pFlux n (g x)-pFlux n (h x)) (gradient η x)|
  have hGI : IntegrableOn (fun x=>‖g x‖^n) W volume := by
    simpa only [IntegrableOn,Real.rpow_natCast] using integrable_norm_rpow_of_memLp su.1 su.2.2.1
  have hHI : IntegrableOn (fun x=>‖h x‖^n) W volume := by
    simpa only [IntegrableOn,Real.rpow_natCast] using integrable_norm_rpow_of_memLp sv.1 sv.2.2.1
  have hdom (x : Space n) (hx : x∈W) : J x ≤ A*(‖g x‖^n + ‖h x‖^n + 2*‖gradient η x‖^n) := by
    calc
      J x ≤ A*((‖pFlux n (g x)‖+‖pFlux n (h x)‖)*‖gradient η x‖) := by
        rw [show J x=|u x-v x| * |inner ℝ (pFlux n (g x)-pFlux n (h x)) (gradient η x)| by exact abs_mul _ _]
        apply mul_le_mul (hgap x hx) _ (abs_nonneg _) hA
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hA
        linarith only [critical_flux_young hn (g x) (gradient η x),
          critical_flux_young hn (h x) (gradient η x)]
  have hM := ((hGI.add hHI).add ((hI.integrableOn (s:=W)).const_mul 2)).const_mul A
  have hgF := (continuous_pFlux su.1).comp_aestronglyMeasurable su.2.2.1.1
  have hhF := (continuous_pFlux sv.1).comp_aestronglyMeasurable sv.2.2.1.1
  have hJm : AEStronglyMeasurable J (volume.restrict W) :=
    ((su.2.1.1.sub sv.2.1.1).mul ((hgF.sub hhF).inner hc.aestronglyMeasurable)).norm
  have hJI : IntegrableOn J W volume := hM.mono_nonneg hJm
    (Eventually.of_forall (fun x => abs_nonneg _))
    (by filter_upwards [ae_restrict_mem hW.measurableSet] with x hx;exact hdom x hx)
  have hzero (x : Space n) (hx : x∉W) : J x=0 := by simp only [J,hoff x hx,inner_zero_right,mul_zero,abs_zero]
  have hej : W.indicator J = J := by
    funext x
    by_cases hx : x∈W
    · exact indicator_of_mem hx J
    · rw [indicator_of_notMem hx,hzero x hx]
  have hglobal : Integrable J volume := hej ▸ (integrable_indicator_iff hW.measurableSet).mpr hJI
  refine ⟨hglobal.integrableOn,?_⟩
  change (∫ x in V,J x) ≤ _
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hWV (fun x hx=>hzero x hx.2)]
  have hle := integral_mono_ae hJI hM (by
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx;exact hdom x hx)
  have hμ : (∫ x in W,‖gradient η x‖^n) ≤ ∫ x,‖gradient η x‖^n ∂volume :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x=>pow_nonneg (norm_nonneg _) _)) hI
  have hGH : Integrable (fun x => ‖g x‖^n + ‖h x‖^n) (volume.restrict W) := hGI.add hHI
  apply hle.trans
  change (∫ x in W,A*((‖g x‖^n+‖h x‖^n)+2*‖gradient η x‖^n))≤_
  rw [integral_const_mul,integral_add hGH (hI.integrableOn.const_mul 2),
    integral_add hGI hHI,integral_const_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hμ (by norm_num : (0:ℝ)≤2))) hA

end BMCompactPDE
#print axioms BMCompactPDE.critical_shell_flux_error_bound
