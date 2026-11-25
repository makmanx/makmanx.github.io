import LocalSmoothWeakBridge
import RadialRegularity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Local Sobolev membership from genuine C-infinity regularity on an open domain.
In particular this discharges the previously explicit local Sobolev hypothesis
for the actual singular radial profile from manuscript equation (2.7), on the
punctured space. No smooth extension across the pole is assumed.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

/-- A continuous function on the compact closure of a bounded measurable
Euclidean set is in every Lq space over that set, including L-infinity. -/
theorem memLp_on_bounded_of_continuousOn_closure {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] (q : ℝ≥0∞)
    {D : Set (Space n)} (hD : Bornology.IsBounded D) (hDm : MeasurableSet D)
    {f : Space n → F} (hf : ContinuousOn f (closure D)) :
    MemLp f q (volume.restrict D) := by
  have hK : IsCompact (closure D) := hD.isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.measure_lt_top.ne
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_subset_isCompact hK hDm subset_closure) C
  filter_upwards [ae_restrict_mem hDm] with x hx
  exact hC x (subset_closure hx)

/-- Local C-infinity regularity yields continuity of the actual gradient;
there is no claim of global smoothness across the boundary. -/
theorem continuousOn_gradient_of_contDiffOn {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    ContinuousOn (gradient u) Ω := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderiv_of_isOpen hΩ (by simp))

/-- On each relatively compact bounded open test domain, locally smooth u
and its actual classical gradient form the manuscript's Sobolev pair. -/
theorem sobolevPair_of_contDiffOn {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω D : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hD : LocalDomain D Ω) :
    SobolevPair p D u (gradient u) := by
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p)
      hD.2.1 hD.1.measurableSet (hu.continuousOn.mono hD.2.2)
  · exact memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p)
      hD.2.1 hD.1.measurableSet
      ((continuousOn_gradient_of_contDiffOn hΩ hu).mono hD.2.2)
  · exact hasWeakGradientOn_of_contDiffOn hD.1 (hu.mono hDΩ)

/-- Genuine local C-infinity functions have local W1p membership with their
actual classical gradient, in the concrete weak-gradient graph. -/
theorem locallySobolevPair_of_contDiffOn {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) :
    LocallySobolevPair p Ω u (gradient u) := by
  intro D hD
  exact sobolevPair_of_contDiffOn hp hΩ hu hD

/-- The actual radial profile of equation (2.7), with no assumed Sobolev
membership, is locally W1p off its pole. Parameters are arbitrary except p>1,
since this assertion uses local smoothness rather than the PDE equation. -/
theorem locallySobolevPair_fundamentalPotential (n : ℕ) (σ p : ℝ) (hp : 1 < p) :
    LocallySobolevPair p {x : Space n | x ≠ 0}
      (fundamentalPotential n σ p) (gradient (fundamentalPotential n σ p)) := by
  apply locallySobolevPair_of_contDiffOn hp
  · exact isOpen_ne
  · exact contDiffOn_fundamentalPotential n σ p

end BMCompactPDE

#print axioms BMCompactPDE.memLp_on_bounded_of_continuousOn_closure
#print axioms BMCompactPDE.continuousOn_gradient_of_contDiffOn
#print axioms BMCompactPDE.sobolevPair_of_contDiffOn
#print axioms BMCompactPDE.locallySobolevPair_of_contDiffOn
#print axioms BMCompactPDE.locallySobolevPair_fundamentalPotential
