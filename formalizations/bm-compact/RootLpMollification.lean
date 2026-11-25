import BMCompactChecked
import RootReusedLp
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! Genuine Lp approximate identities for arbitrary Sobolev representatives.
The scalar Young estimate is an attributed existing public proof; vector
contraction and the approximation argument below are proved here. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution
namespace BMCompactPDE
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem eLpNorm_convolution_le_vector {q : ℝ≥0∞} (hq : 1≤q)
    (hqt : q≠(∞ : ℝ≥0∞)) {ρ : Space n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (hρ0 : ∀ y, 0≤ρ y) (hρ1 : ∫ y, ρ y=1)
    {f : Space n → F} (hf : MemLp f q volume) :
    eLpNorm (ρ ⋆[lsmul ℝ ℝ,volume] f) q volume ≤ eLpNorm f q volume := by
  have hb (x : Space n) : ‖(ρ ⋆[lsmul ℝ ℝ,volume] f) x‖ ≤
      (ρ ⋆[lsmul ℝ ℝ,volume] fun y => ‖f y‖) x := by
    calc
      _ ≤ ∫ y, ‖ρ y • f (x-y)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        simp only [convolution,lsmul_apply,smul_eq_mul,norm_smul,
          Real.norm_eq_abs,abs_of_nonneg (hρ0 _)]
  rw [←eLpNorm_norm f]
  exact (eLpNorm_mono_ae_real (Eventually.of_forall hb)).trans
    (BMCompactReuse.scalar_convolution_contraction hq hqt ρ hρ hc hρ0 hρ1 _ hf.norm)

theorem memLp_normalizedMollify {q : ℝ≥0∞} (hq : 1≤q)
    (hqt : q≠(∞ : ℝ≥0∞)) (b : ContDiffBump (0 : Space n))
    {f : Space n → F} (hf : MemLp f q volume) :
    MemLp (normalizedMollify b f) q volume := by
  refine ⟨?_,?_⟩
  · exact (b.hasCompactSupport_normed.continuous_convolution_left
      (lsmul ℝ ℝ) b.continuous_normed (hf.locallyIntegrable hq)).aestronglyMeasurable
  · exact (eLpNorm_convolution_le_vector hq hqt b.continuous_normed
      b.hasCompactSupport_normed b.nonneg_normed b.integral_normed hf).trans_lt hf.2

theorem normalizedMollify_sub {q : ℝ≥0∞} (hq : 1≤q)
    (b : ContDiffBump (0 : Space n)) {f h : Space n → F}
    (hf : MemLp f q volume) (hh : MemLp h q volume) :
    normalizedMollify b (f-h) = normalizedMollify b f-normalizedMollify b h := by
  have hfi := (b.hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
    (lsmul ℝ ℝ) b.continuous_normed (hf.locallyIntegrable hq)
  have hhi := (b.hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
    (lsmul ℝ ℝ) b.continuous_normed (hh.locallyIntegrable hq)
  funext x
  change (∫ y, b.normed volume y • (f (x-y)-h (x-y))) =
    (∫ y, b.normed volume y • f (x-y))-(∫ y, b.normed volume y • h (x-y))
  simp_rw [smul_sub]
  exact integral_sub (hfi x).integrable (hhi x).integrable

/-- Actual finite-Lp convergence of genuine normalized bump convolutions.
No continuity or pointwise convergence of the original f is assumed. -/
theorem tendsto_eLpNorm_mollify_sub_of_memLp {q : ℝ≥0∞} (hq : 1≤q)
    (hqt : q≠(∞ : ℝ≥0∞)) {b : ℕ → ContDiffBump (0 : Space n)}
    (hblim : Tendsto (fun j => (b j).rOut) atTop (𝓝 0))
    {R : ℝ} (hR : 0≤R) (hbR : ∀ j, (b j).rOut≤R)
    {f : Space n → F} (hf : MemLp f q volume) :
    Tendsto (fun j => eLpNorm (normalizedMollify (b j) f-f) q volume) atTop (𝓝 0) := by
  have hq0 : q≠0 := (zero_lt_one.trans_le hq).ne'
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases hεtop : ε=(∞ : ℝ≥0∞)
  · exact Eventually.of_forall (fun _ => by rw [hεtop]; exact le_top)
  have hεr : 0<ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  let δ : ℝ := ε.toReal/4
  have hδ : 0<δ := div_pos hεr (by norm_num)
  obtain ⟨h,hc,hs,hhf⟩ := hf.exist_eLpNorm_sub_le hqt hq hδ
  have hhm : MemLp h q volume := hs.continuous.memLp_of_hasCompactSupport hc
  have hmh := tendsto_eLpNorm_mollify_sub (μ := volume) hq0 hqt hblim hR hbR hs.continuous hc
  have hsmall := (ENNReal.tendsto_nhds_zero.mp hmh)
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [hsmall] with j hj
  have hmf := memLp_normalizedMollify hq hqt (b j) hf
  have hmhmem := memLp_normalizedMollify hq hqt (b j) hhm
  have heq : normalizedMollify (b j) f-f =
      normalizedMollify (b j) (f-h)+((normalizedMollify (b j) h-h)+(h-f)) := by
    rw [normalizedMollify_sub hq (b j) hf hhm]
    abel
  have hnorm : eLpNorm (normalizedMollify (b j) f-f) q volume ≤
      eLpNorm (f-h) q volume+
        (eLpNorm (normalizedMollify (b j) h-h) q volume+eLpNorm (h-f) q volume) := by
    rw [heq]
    exact (eLpNorm_add_le
      (memLp_normalizedMollify hq hqt (b j) (hf.sub hhm)).1
      ((hmhmem.sub hhm).add (hhm.sub hf)).1 hq).trans
      (add_le_add (eLpNorm_convolution_le_vector hq hqt
        (b j).continuous_normed (b j).hasCompactSupport_normed
        (b j).nonneg_normed (b j).integral_normed (hf.sub hhm))
        (eLpNorm_add_le (hmhmem.sub hhm).1 (hhm.sub hf).1 hq))
  have hbnd := hnorm.trans (add_le_add hhf (add_le_add hj (by
    simpa only [eLpNorm_sub_comm] using hhf)))
  apply hbnd.trans
  rw [←ENNReal.ofReal_add hδ.le hδ.le,
    ←ENNReal.ofReal_add hδ.le (add_nonneg hδ.le hδ.le),←ENNReal.ofReal_toReal hεtop]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [δ]
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.eLpNorm_convolution_le_vector
#print axioms BMCompactPDE.memLp_normalizedMollify
#print axioms BMCompactPDE.normalizedMollify_sub
#print axioms BMCompactPDE.tendsto_eLpNorm_mollify_sub_of_memLp
