import WeakPoincare
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Pointwise consequences of the derived Poincare/weak-energy uniqueness
for actual continuous representatives on open Euclidean test domains. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory

namespace BMCompactPDE

theorem ZeroBoundarySobolevPair.eqOn_zero_of_gradient_ae_zero
    {n : ℕ} {p : ℝ} {D : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : ZeroBoundarySobolevPair p D u g)
    (hn : 2 ≤ n) (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (hg : g =ᵐ[volume.restrict D] 0) (huc : ContinuousOn u D) :
    EqOn u 0 D := by
  exact Measure.eqOn_open_of_ae_eq
    (hu.ae_eq_zero_of_gradient_ae_zero hn hD hDb hg) hD huc continuousOn_const

theorem WeakPHarmonicPair.eqOn_of_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hn : 2 ≤ n) (hD : LocalDomain D Ω)
    (hboundary : ZeroBoundarySobolevPair p D (u - v) (g - h))
    (huc : ContinuousOn u D) (hvc : ContinuousOn v D) : EqOn u v D := by
  exact Measure.eqOn_open_of_ae_eq
    (hu.ae_eq_of_zeroBoundaryDifference hv hn hD hboundary) hD.1 huc hvc

end BMCompactPDE

#print axioms BMCompactPDE.ZeroBoundarySobolevPair.eqOn_zero_of_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.eqOn_of_zeroBoundaryDifference
