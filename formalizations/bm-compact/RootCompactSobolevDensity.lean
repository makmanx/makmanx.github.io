import RootLpMollification
import RootWeakMollification
import RootSobolevLocalization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! Genuine compact-support density in the distributional W1p graph.
The arbitrary input is not assumed continuous or classically differentiable;
actual mollification, weak-gradient commutation and Lp convergence construct
all smooth approximants and both limiting components. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace ContinuousLinearMap
open scoped Topology ContDiff ENNReal Pointwise Convolution
namespace BMCompactPDE

theorem zeroBoundarySobolevPair_of_sobolev_compactSupport {n : ℕ} {p : ℝ}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) {D K : Set (Space n)} (hD : IsOpen D)
    (hK : IsCompact K) (huK : tsupport u ⊆ K) (_hgK : tsupport g ⊆ K)
    (hKD : K ⊆ D) : ZeroBoundarySobolevPair p D u g := by
  obtain ⟨δ,hδ,hδD⟩ := hK.exists_cthickening_subset_open hD hKD
  let R : ℕ → ℝ := fun j => δ/((j : ℝ)+1)
  have hRp (j : ℕ) : 0<R j := div_pos hδ (by positivity)
  have hRb (j : ℕ) : R j≤δ := by
    dsimp only [R]
    apply (div_le_iff₀ (by positivity : 0<(j : ℝ)+1)).mpr
    nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) j)]
  let b : ℕ → ContDiffBump (0 : Space n) := fun j =>
    ⟨R j/2,R j,half_pos (hRp j),half_lt_self (hRp j)⟩
  have hbl : Tendsto (fun j => (b j).rOut) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [b,R,div_eq_mul_inv,mul_zero,Function.comp_apply] using!
      (tendsto_const_nhds (x := δ)).mul (tendsto_inv_atTop_zero.comp hn)
  have hq : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hu.1.le
  have hqt : ENNReal.ofReal p≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa using hu.2.1
  have hgm : MemLp g (ENNReal.ofReal p) volume := by simpa using hu.2.2.1
  have huc : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) huK
  let φ : ℕ → Space n → ℝ := fun j => normalizedMollify (b j) u
  have hφ (j : ℕ) : SmoothTest D (φ j) := by
    refine ⟨((b j).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (lsmul ℝ ℝ) (b j).contDiff_normed (hum.locallyIntegrable hq),
      hasCompactSupport_normalizedMollify (b j) huc,?_⟩
    apply (tsupport_normalizedMollify_subset (b j) huc).trans
    rintro x ⟨a,ha,y,hy,rfl⟩
    apply hδD
    apply mem_cthickening_of_dist_le (a+y) y δ K (huK hy)
    simpa only [dist_eq_norm,add_sub_cancel_right] using
      (mem_closedBall_zero_iff.mp ha).trans (hRb j)
  have hcomm (j : ℕ) : gradient (φ j) = normalizedMollify (b j) g :=
    hu.gradient_convolution_eq (b j).contDiff_normed (b j).hasCompactSupport_normed
  have hLu := tendsto_eLpNorm_mollify_sub_of_memLp hq hqt hbl hδ.le hRb hum
  have hLg := tendsto_eLpNorm_mollify_sub_of_memLp hq hqt hbl hδ.le hRb hgm
  have hLuD : Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal p)
      (volume.restrict D)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLu
      (fun _ => bot_le)
    intro j
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hLgD : Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x)
      (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
    simp_rw [hcomm]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLg
      (fun _ => bot_le)
    intro j
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  exact ⟨sobolevPair_of_eLpNorm_limits hu.1 (fun j => (hφ j).sobolevPair hu.1)
    (hum.restrict D) (hgm.restrict D) hLuD hLgD,φ,hφ,hLuD,hLgD⟩

/-- Actual compact smooth localization of an arbitrary Sobolev pair is an
admissible full-W0 test. Neither regularity nor density is a premise. -/
theorem SobolevPair.mul_smooth_compactSupport_zeroBoundary {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hD : IsOpen D) {χ : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ D) :
    ZeroBoundarySobolevPair p D (fun x => χ x*u x)
      (fun x => χ x • g x+u x • gradient χ x) := by
  have hglo := hu.mul_smooth_compactSupport_global hD hχ hc hs
  apply zeroBoundarySobolevPair_of_sobolev_compactSupport hglo hD hc.isCompact
    tsupport_mul_subset_left _ hs
  exact (tsupport_add _ _).trans (union_subset (tsupport_smul_subset_left χ g)
    ((tsupport_smul_subset_right u (gradient χ)).trans (tsupport_gradient_subset_actual χ)))

end BMCompactPDE
#print axioms BMCompactPDE.zeroBoundarySobolevPair_of_sobolev_compactSupport
#print axioms BMCompactPDE.SobolevPair.mul_smooth_compactSupport_zeroBoundary
