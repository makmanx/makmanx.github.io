import WeakGlobalTesting
import WeakContinuousUniqueness
import Mathlib.Topology.Order.Lattice

/-!
An actual positive-part-test comparison foundation. The standard candidate
positive-part weak gradient is displayed in the hypothesis, and its membership
in the zero-boundary Sobolev graph is explicitly assumed, not inferred from
boundary ordering or an unproved Sobolev chain rule. The PDE conclusion is
proved by whole-domain testing, strict monotonicity and the derived Poincare
criterion. This is not yet an unrestricted boundary comparison principle.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace BMCompactPDE

/-- The actual positive-part difference gradient vanishes a.e. when that
positive-part pair is an available W0 test for two finite-energy solutions. -/
theorem WeakPHarmonicPair.positivePart_gradient_ae_zero
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hpositive : ZeroBoundarySobolevPair p Ω
      (fun x => max (u x - v x) 0)
      (fun x => if v x < u x then g x - h x else 0)) :
    (fun x => if v x < u x then g x - h x else 0) =ᵐ[volume.restrict Ω] 0 := by
  let θ : Space n → ℝ := fun x => max (u x - v x) 0
  let w : Space n → Space n := fun x => if v x < u x then g x - h x else 0
  have hθ : ZeroBoundarySobolevPair p Ω θ w := hpositive
  obtain ⟨hgi, hgeq⟩ := hu.integral_zeroBoundary_eq_zero hSu hθ
  obtain ⟨hhi, hheq⟩ := hv.integral_zeroBoundary_eq_zero hSv hθ
  let pairing : Space n → ℝ := fun x =>
    inner ℝ (pFlux p (g x) - pFlux p (h x)) (w x)
  have hpair : pairing = fluxPairing p g w - fluxPairing p h w := by
    funext x
    simp only [pairing, fluxPairing, Pi.sub_apply, inner_sub_left]
  have hpi : Integrable pairing (volume.restrict Ω) := by
    rw [hpair]
    exact hgi.sub hhi
  have hpeq : (∫ x in Ω, pairing x) = 0 := by
    rw [hpair]
    simp only [Pi.sub_apply]
    rw [integral_sub hgi hhi, hgeq, hheq, sub_self]
  have hnonneg : 0 ≤ᵐ[volume.restrict Ω] pairing := by
    apply Eventually.of_forall
    intro x
    by_cases hx : v x < u x
    · simp only [pairing, w, if_pos hx]
      exact pFlux_monotonicity hu.1 (g x) (h x)
    · simp only [pairing, w, if_neg hx, inner_zero_right]
      exact le_rfl
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hpi).1 hpeq
  change w =ᵐ[volume.restrict Ω] 0
  filter_upwards [hzero] with x hx
  by_cases hvu : v x < u x
  · have hgh : g x = h x :=
      (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).1 (by
        simpa only [pairing, w, if_pos hvu, Pi.zero_apply] using hx)
    simp only [w, if_pos hvu, hgh, sub_self, Pi.zero_apply]
  · simp only [w, if_neg hvu, Pi.zero_apply]

/-- On a bounded open domain of dimension at least two, an actual W0
positive-part pair gives almost-everywhere order of finite-energy solutions. -/
theorem WeakPHarmonicPair.ae_le_of_zeroBoundary_positivePart
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hpositive : ZeroBoundarySobolevPair p Ω
      (fun x => max (u x - v x) 0)
      (fun x => if v x < u x then g x - h x else 0)) :
    u ≤ᵐ[volume.restrict Ω] v := by
  have hw := hu.positivePart_gradient_ae_zero hv hSu hSv hpositive
  have hθ := hpositive.ae_eq_zero_of_gradient_ae_zero hn hu.2.1 hΩb hw
  filter_upwards [hθ] with x hx
  have hmax : max (u x - v x) 0 = 0 := hx
  have hdiff : u x - v x ≤ 0 := (le_max_left (u x - v x) 0).trans hmax.le
  exact sub_nonpos.mp hdiff

/-- For actual continuous representatives the same available positive-part
W0 test gives pointwise order throughout the bounded open domain. -/
theorem WeakPHarmonicPair.leOn_of_zeroBoundary_positivePart
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hpositive : ZeroBoundarySobolevPair p Ω
      (fun x => max (u x - v x) 0)
      (fun x => if v x < u x then g x - h x else 0))
    (huc : ContinuousOn u Ω) (hvc : ContinuousOn v Ω) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have hw := hu.positivePart_gradient_ae_zero hv hSu hSv hpositive
  have hθc : ContinuousOn (fun x => max (u x - v x) 0) Ω :=
    (huc.sub hvc).sup continuousOn_const
  have hθ := hpositive.eqOn_zero_of_gradient_ae_zero hn hu.2.1 hΩb hw hθc
  intro x hx
  have hmax : max (u x - v x) 0 = 0 := hθ hx
  have hdiff : u x - v x ≤ 0 := (le_max_left (u x - v x) 0).trans hmax.le
  exact sub_nonpos.mp hdiff

end BMCompactPDE

#print axioms BMCompactPDE.WeakPHarmonicPair.positivePart_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_le_of_zeroBoundary_positivePart
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_zeroBoundary_positivePart
