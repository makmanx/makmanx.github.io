import WeakPoincare
import WeakDensity
import SmoothWeakBridge
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
From the manuscript's local weak equation to the whole-domain zero-boundary
Sobolev test equation, under actual finite-energy Sobolev membership.
Every compact smooth test is enclosed in an explicitly constructed bounded
open relatively compact thickening. Holder/density supplies the global test
extension. Consequently bounded-domain W0 Dirichlet uniqueness does not require
the false side condition closure(Omega) subset Omega.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

/-- Actual local weak p-harmonicity implies the equation for every genuine
smooth compact-support test in the entire open domain. -/
theorem WeakPHarmonicPair.integral_smooth_test_eq_zero
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    (∫ x in Ω, fluxPairing p g (gradient φ) x) = 0 := by
  obtain ⟨δ, hδ, hδΩ⟩ := hφ.2.1.exists_cthickening_subset_open hu.2.1 hφ.2.2
  let D : Set (Space n) := Metric.thickening δ (tsupport φ)
  have hKD : tsupport φ ⊆ D := Metric.self_subset_thickening hδ (tsupport φ)
  have hD : LocalDomain D Ω :=
    ⟨Metric.isOpen_thickening, hφ.2.1.isBounded.thickening,
      (Metric.closure_thickening_subset_cthickening δ (tsupport φ)).trans hδΩ⟩
  have hφD : SmoothTest D φ := ⟨hφ.1, hφ.2.1, hKD⟩
  have hφW0 := hφD.zeroBoundarySobolevPair hu.1
  have hlocal := (hu.2.2.2 D hD φ (gradient φ) hφW0).2
  have hz (x : Space n) (hx : x ∉ tsupport φ) :
      fluxPairing p g (gradient φ) x = 0 := by
    simp only [fluxPairing, BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hx,
      inner_zero_right]
  have hglobalD : (∫ x in D, fluxPairing p g (gradient φ) x) =
      ∫ x, fluxPairing p g (gradient φ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      hz x (fun ht => hx (hKD ht)))
  have hglobalΩ : (∫ x in Ω, fluxPairing p g (gradient φ) x) =
      ∫ x, fluxPairing p g (gradient φ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      hz x (fun ht => hx (hφ.2.2 ht)))
  rw [hglobalΩ, ← hglobalD]
  exact hlocal

/-- If the actual weak pair has global finite Sobolev energy on its domain,
its equation holds against every whole-domain W0 test; no compact containment
of the whole domain in itself is required. -/
theorem WeakPHarmonicPair.integral_zeroBoundary_eq_zero
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hSob : SobolevPair p Ω u g)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ h) :
    Integrable (fluxPairing p g h) (volume.restrict Ω) ∧
      (∫ x in Ω, fluxPairing p g h x) = 0 := by
  haveI := holderConjugate_p_dual hu.1
  exact zeroBoundary_integral_eq_zero_of_smoothTests
    (memLp_pFlux hu.1 hSob.2.2.1)
    (fun φ hφ => hu.integral_smooth_test_eq_zero hφ) hθ

/-- Global finite-energy W0 Dirichlet data give equality of the actual weak
gradient fields throughout the open domain. -/
theorem WeakPHarmonicPair.gradient_ae_eq_of_global_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hboundary : ZeroBoundarySobolevPair p Ω (u - v) (g - h)) :
    g =ᵐ[volume.restrict Ω] h := by
  obtain ⟨hgi, hgeq⟩ := hu.integral_zeroBoundary_eq_zero hSu hboundary
  obtain ⟨hhi, hheq⟩ := hv.integral_zeroBoundary_eq_zero hSv hboundary
  let pairing : Space n → ℝ := fun x =>
    inner ℝ (pFlux p (g x) - pFlux p (h x)) (g x - h x)
  have hpair : pairing = fluxPairing p g (g - h) - fluxPairing p h (g - h) := by
    funext x
    simp only [pairing, fluxPairing, Pi.sub_apply, inner_sub_left]
  have hpi : Integrable pairing (volume.restrict Ω) := by
    rw [hpair]
    exact hgi.sub hhi
  have hpeq : (∫ x in Ω, pairing x) = 0 := by
    rw [hpair]
    simp only [Pi.sub_apply]
    rw [integral_sub hgi hhi, hgeq, hheq, sub_self]
  have hnonneg : 0 ≤ᵐ[volume.restrict Ω] pairing :=
    Eventually.of_forall (fun x => pFlux_monotonicity hu.1 (g x) (h x))
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hpi).1 hpeq
  filter_upwards [hzero] with x hx
  exact (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).1 hx

/-- Genuine bounded-domain finite-energy W0 Dirichlet uniqueness, proved
from local weak equations, Holder density, strict monotonicity and Poincare. -/
theorem WeakPHarmonicPair.ae_eq_of_global_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ZeroBoundarySobolevPair p Ω (u - v) (g - h)) :
    u =ᵐ[volume.restrict Ω] v := by
  have hgrad := hu.gradient_ae_eq_of_global_zeroBoundaryDifference hv hSu hSv hboundary
  have hdiff : (g - h) =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hgrad] with x hx
    simp only [Pi.sub_apply, hx, sub_self, Pi.zero_apply]
  have hzero := hboundary.ae_eq_zero_of_gradient_ae_zero hn hu.2.1 hΩb hdiff
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/-- For actual continuous representatives, bounded-domain finite-energy W0
Dirichlet uniqueness is pointwise on the entire open domain. -/
theorem WeakPHarmonicPair.eqOn_of_global_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ZeroBoundarySobolevPair p Ω (u - v) (g - h))
    (huc : ContinuousOn u Ω) (hvc : ContinuousOn v Ω) : EqOn u v Ω := by
  exact Measure.eqOn_open_of_ae_eq
    (hu.ae_eq_of_global_zeroBoundaryDifference hv hSu hSv hn hΩb hboundary)
    hu.2.1 huc hvc

end BMCompactPDE

#print axioms BMCompactPDE.WeakPHarmonicPair.integral_smooth_test_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.integral_zeroBoundary_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.gradient_ae_eq_of_global_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_eq_of_global_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.eqOn_of_global_zeroBoundaryDifference
