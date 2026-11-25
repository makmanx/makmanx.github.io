import SupConvolutionProperties
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring

/-!
The actual envelope's radial tail bound and the stronger critical/supercritical
relative decay in source (5.6)(d). The hypotheses on F and the three functions
are precisely the eventual fundamental-solution bounds used in the printed
proof; no estimate on the envelope is a hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactEnvelope
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- In a convex weighted decomposition, at least one point is as far from
the origin as the resulting point. -/
theorem norm_le_one_of_blend {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x y z : V} (hx : x = t • y + (1 - t) • z) :
    ‖x‖ ≤ ‖y‖ ∨ ‖x‖ ≤ ‖z‖ := by
  have hn : ‖x‖ ≤ t * ‖y‖ + (1 - t) * ‖z‖ := by
    rw [hx]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0,
      abs_of_nonneg (sub_nonneg.mpr ht1)] using
      norm_add_le (t • y) ((1 - t) • z)
  by_contra h
  push Not at h
  have htz := mul_le_mul_of_nonneg_left h.2.le (sub_nonneg.mpr ht1)
  by_cases ht : t = 0
  · subst t
    have hxz : x = z := by simpa using hx
    exact (lt_irrefl ‖z‖) (by simpa only [hxz] using h.2)
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hstrict := mul_lt_mul_of_pos_left h.1 htpos
    nlinarith

/-- Source (5.7), with the component radial upper bounds inserted into the
actual constrained supremum. -/
theorem supConvolution_le_radial_majorant {t R C : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {u v F : V → ℝ}
    (hFmono : ∀ {x y : V}, R ≤ ‖x‖ → ‖x‖ ≤ ‖y‖ → F x ≤ F y)
    (hu : ∀ y, R ≤ ‖y‖ → u y ≤ -F y + C)
    (hv : ∀ z, R ≤ ‖z‖ → v z ≤ -F z + C)
    {x : V} (hxR : R ≤ ‖x‖) :
    supConvolution t u v x ≤ -F x + C := by
  apply csSup_le (fibreValues_nonempty t u v x)
  rintro r ⟨y, z, hxyz, rfl⟩
  obtain hy | hz := norm_le_one_of_blend ht0 ht1 hxyz
  · exact (min_le_left _ _).trans ((hu y (hxR.trans hy)).trans
      (by linarith [hFmono hxR hy]))
  · exact (min_le_right _ _).trans ((hv z (hxR.trans hz)).trans
      (by linarith [hFmono hxR hz]))

/-- The explicit source bound w*−theta*w≤−(1−theta)F+2C outside a ball. -/
theorem supConvolution_relative_radial_bound {t R C theta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) {u v w F : V → ℝ}
    (hFmono : ∀ {x y : V}, R ≤ ‖x‖ → ‖x‖ ≤ ‖y‖ → F x ≤ F y)
    (hu : ∀ y, R ≤ ‖y‖ → u y ≤ -F y + C)
    (hv : ∀ z, R ≤ ‖z‖ → v z ≤ -F z + C)
    (hw : ∀ x, R ≤ ‖x‖ → -F x - C ≤ w x)
    {x : V} (hxR : R ≤ ‖x‖) :
    supConvolution t u v x - theta * w x ≤ -(1 - theta) * F x + 2 * C := by
  have he := supConvolution_le_radial_majorant ht0 ht1 hFmono hu hv hxR
  have hw' := mul_le_mul_of_nonneg_left (hw x hxR) hθ0
  have hC' := mul_le_mul_of_nonneg_right hθ1 hC
  nlinarith

/-- Source critical/supercritical (5.6)(d), derived from explicit asymptotic
fundamental-solution bounds on the component functions and comparison function.
The radial profile F may be logarithmic or a positive power. -/
theorem tendsto_supConvolution_sub_smul_atBot {t R C theta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) {u v w F : V → ℝ}
    (hFmono : ∀ {x y : V}, R ≤ ‖x‖ → ‖x‖ ≤ ‖y‖ → F x ≤ F y)
    (hFlim : Tendsto F (cobounded V) atTop)
    (hu : ∀ y, R ≤ ‖y‖ → u y ≤ -F y + C)
    (hv : ∀ z, R ≤ ‖z‖ → v z ≤ -F z + C)
    (hw : ∀ x, R ≤ ‖x‖ → -F x - C ≤ w x) :
    Tendsto (fun x => supConvolution t u v x - theta * w x)
      (cobounded V) atBot := by
  apply tendsto_atBot.2
  intro b
  have hpos : 0 < 1 - theta := sub_pos.mpr hθ1
  filter_upwards [eventually_cobounded_le_norm R,
    hFlim.eventually_ge_atTop ((2 * C - b) / (1 - theta))] with x hxR hxF
  have hbound := supConvolution_relative_radial_bound ht0 ht1 hC hθ0 hθ1.le
    hFmono hu hv hw hxR
  have hmul := (div_le_iff₀ hpos).mp hxF
  nlinarith

end BMCompactEnvelope

#print axioms BMCompactEnvelope.norm_le_one_of_blend
#print axioms BMCompactEnvelope.supConvolution_le_radial_majorant
#print axioms BMCompactEnvelope.supConvolution_relative_radial_bound
#print axioms BMCompactEnvelope.tendsto_supConvolution_sub_smul_atBot
