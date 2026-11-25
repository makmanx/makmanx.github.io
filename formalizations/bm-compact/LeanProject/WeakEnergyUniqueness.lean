import WeakPDE
import GreenFoundation

/-!
The monotonicity argument for the nonlinear weak equation. If two weak
solutions admit their difference as a zero-boundary Sobolev test on a
relatively compact subdomain, their weak gradients agree almost everywhere
there. A Poincare argument identifying the function values, and the positive-
part chain rule needed for a full comparison theorem, are not asserted here.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace BMCompactPDE

theorem WeakPHarmonicPair.gradient_ae_eq_of_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hD : LocalDomain D Ω)
    (hboundary : ZeroBoundarySobolevPair p D (u - v) (g - h)) :
    g =ᵐ[volume.restrict D] h := by
  obtain ⟨hgi, hgeq⟩ := hu.2.2.2 D hD (u - v) (g - h) hboundary
  obtain ⟨hhi, hheq⟩ := hv.2.2.2 D hD (u - v) (g - h) hboundary
  let pairing : Space n → ℝ := fun x =>
    inner ℝ (pFlux p (g x) - pFlux p (h x)) (g x - h x)
  have hpair : pairing = fluxPairing p g (g - h) - fluxPairing p h (g - h) := by
    funext x
    simp only [pairing, fluxPairing, Pi.sub_apply, inner_sub_left]
  have hpi : Integrable pairing (volume.restrict D) := by
    rw [hpair]
    exact hgi.sub hhi
  have hpeq : (∫ x in D, pairing x) = 0 := by
    rw [hpair]
    simp only [Pi.sub_apply]
    rw [integral_sub hgi hhi, hgeq, hheq, sub_self]
  have hnonneg : 0 ≤ᵐ[volume.restrict D] pairing :=
    Eventually.of_forall (fun x => pFlux_monotonicity hu.1 (g x) (h x))
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hpi).1 hpeq
  filter_upwards [hzero] with x hx
  exact (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).1 hx

end BMCompactPDE

#print axioms BMCompactPDE.WeakPHarmonicPair.gradient_ae_eq_of_zeroBoundaryDifference
