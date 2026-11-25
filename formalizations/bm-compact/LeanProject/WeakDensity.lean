import WeakPDE
import CapacityFoundation
import GreenFoundation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
Hölder continuity of the actual weak flux functional and extension from
smooth compact-support tests to all W^{1,p}_0 pairs.  The extension uses the
gradient approximation in the definition of W^{1,p}_0 and L¹ continuity of
the Bochner integral.  No weak PDE equation is assumed for nonsmooth tests.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology ContDiff InnerProductSpace

namespace BMCompactPDE

theorem holderConjugate_p_dual {p : ℝ} (hp : 1 < p) :
    ENNReal.HolderConjugate (ENNReal.ofReal (p / (p - 1))) (ENNReal.ofReal p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hm : 0 < p - 1 := sub_pos.mpr hp
  apply ENNReal.holderConjugate_iff.mpr
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hp0 hm),
    ← ENNReal.ofReal_inv_of_pos hp0,
    ← ENNReal.ofReal_add (inv_nonneg.mpr (div_nonneg hp0.le hm.le)) (inv_nonneg.mpr hp0.le)]
  have heq : (p / (p - 1))⁻¹ + p⁻¹ = 1 := by
    field_simp
    ring
  rw [heq, ENNReal.ofReal_one]

/-- The p-flux of an L^p field has exactly the dual integrability exponent. -/
theorem memLp_pFlux {n : ℕ} {p : ℝ} (hp : 1 < p)
    {μ : Measure (Space n)} {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    MemLp (fun x => pFlux p (g x)) (ENNReal.ofReal (p / (p - 1))) μ := by
  have hm : 0 < p - 1 := sub_pos.mpr hp
  have hn : MemLp (fun x => ‖g x‖ ^ (p - 1))
      (ENNReal.ofReal (p / (p - 1))) μ := by
    simpa only [ENNReal.toReal_ofReal hm.le, ← ENNReal.ofReal_div_of_pos hm]
      using hg.norm_rpow_div (ENNReal.ofReal (p - 1))
  have hmeas : AEStronglyMeasurable (fun x => pFlux p (g x)) μ :=
    (continuous_pFlux hp).comp_aestronglyMeasurable hg.1
  apply (memLp_norm_iff hmeas).mp
  simpa only [norm_pFlux hp] using hn

theorem inner_integrable_of_memLp {n : ℕ} {P Q : ℝ≥0∞}
    [ENNReal.HolderConjugate P Q] {μ : Measure (Space n)}
    {F h : Space n → Space n} (hF : MemLp F P μ) (hh : MemLp h Q μ) :
    Integrable (fun x => inner ℝ (F x) (h x)) μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bilin (fun a b : Space n => inner ℝ a b) (1 : ℝ≥0) hF hh
    (hF.1.inner hh.1) (Eventually.of_forall (fun x => by
      simpa only [one_mul] using nnnorm_inner_le_nnnorm (𝕜 := ℝ) (F x) (h x)))

/-- Density extension for a genuine vector field in the Hölder dual space. -/
theorem zeroBoundary_integral_eq_zero_of_smoothTests {n : ℕ} {p : ℝ}
    {Q : ℝ≥0∞} [ENNReal.HolderConjugate Q (ENNReal.ofReal p)]
    {D : Set (Space n)} {F : Space n → Space n}
    (hF : MemLp F Q (volume.restrict D))
    (hzero : ∀ φ : Space n → ℝ, SmoothTest D φ →
      (∫ x in D, inner ℝ (F x) (gradient φ x)) = 0)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p D θ h) :
    Integrable (fun x => inner ℝ (F x) (h x)) (volume.restrict D) ∧
      (∫ x in D, inner ℝ (F x) (h x)) = 0 := by
  obtain ⟨hSob, φ, hφ, _, hgradlim⟩ := hθ
  have hmem : MemLp h (ENNReal.ofReal p) (volume.restrict D) := hSob.2.2.1
  have hmemφ (j : ℕ) : MemLp (gradient (φ j)) (ENNReal.ofReal p) (volume.restrict D) :=
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp
      (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1).restrict D
  have hint : Integrable (fun x => inner ℝ (F x) (h x)) (volume.restrict D) :=
    inner_integrable_of_memLp hF hmem
  have hintφ (j : ℕ) : Integrable (fun x => inner ℝ (F x) (gradient (φ j) x))
      (volume.restrict D) := inner_integrable_of_memLp hF (hmemφ j)
  have hbound (j : ℕ) :
      eLpNorm ((fun x => inner ℝ (F x) (gradient (φ j) x)) -
        (fun x => inner ℝ (F x) (h x))) 1 (volume.restrict D) ≤
      eLpNorm F Q (volume.restrict D) *
        eLpNorm (fun x => gradient (φ j) x - h x) (ENNReal.ofReal p) (volume.restrict D) := by
    have hineq := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (p := Q) (q := ENNReal.ofReal p) (r := 1)
      hF.1 ((hmemφ j).sub hmem).1
      (fun a b : Space n => inner ℝ a b) (1 : ℝ≥0)
      (Eventually.of_forall (fun x => by
        simpa only [NNReal.coe_one, one_mul, Pi.sub_apply] using
          norm_inner_le_norm (𝕜 := ℝ) (F x) (gradient (φ j) x - h x)))
    simpa only [ENNReal.coe_one, one_mul, Pi.sub_def, inner_sub_right] using hineq
  have hlim : Tendsto (fun j =>
      eLpNorm ((fun x => inner ℝ (F x) (gradient (φ j) x)) -
        (fun x => inner ℝ (F x) (h x))) 1 (volume.restrict D)) atTop (𝓝 0) := by
    have hboundlim : Tendsto (fun j : ℕ => eLpNorm F Q (volume.restrict D) *
        eLpNorm (fun x => gradient (φ j) x - h x)
          (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hgradlim (Or.inr hF.eLpNorm_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hboundlim (fun _ => bot_le) hbound
  have hlimint := tendsto_integral_of_L1'
    (fun x => inner ℝ (F x) (h x)) hint.1
    (Eventually.of_forall hintφ) hlim
  have hzeroφ : (fun j => ∫ x in D, inner ℝ (F x) (gradient (φ j) x)) =
      (fun _ : ℕ => (0 : ℝ)) := funext (fun j => hzero (φ j) (hφ j))
  refine ⟨hint, ?_⟩
  apply tendsto_nhds_unique hlimint
  rw [hzeroφ]
  exact tendsto_const_nhds

/-- For p>1, the smooth-test p-Laplace equation extends to the complete
zero-boundary Sobolev test class used in the manuscript. -/
theorem weakPHarmonicPair_of_smooth_test_equation {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (htest : ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ φ : Space n → ℝ, SmoothTest D φ →
        (∫ x in D, fluxPairing p g (gradient φ) x) = 0) :
    WeakPHarmonicPair p Ω u g := by
  haveI := holderConjugate_p_dual hp
  refine ⟨hp, hΩ, hSob, ?_⟩
  intro D hD θ h hθ
  exact zeroBoundary_integral_eq_zero_of_smoothTests
    (memLp_pFlux hp (hSob D hD).2.2.1) (htest D hD) hθ

end BMCompactPDE

#print axioms BMCompactPDE.holderConjugate_p_dual
#print axioms BMCompactPDE.memLp_pFlux
#print axioms BMCompactPDE.inner_integrable_of_memLp
#print axioms BMCompactPDE.zeroBoundary_integral_eq_zero_of_smoothTests
#print axioms BMCompactPDE.weakPHarmonicPair_of_smooth_test_equation
