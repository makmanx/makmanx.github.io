import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

/-!
Algebraic/limit substep of `lem:cone-comparison`, manuscript lines 2747--2763.

This file does not formalize the p-Laplacian, a Riesz measure, the source-capacity
bound, or the cone-comparison lemma.  It checks the final iteration/limit
contradiction after those analytic facts have supplied a positive scaling
coefficient and a density sequence tending to zero.
-/

open Filter Topology

namespace BMCompact

/-- Iterating `mass (s*r) ≥ a*mass r` along positive geometric radii.

In the manuscript, `mass r = σ(B(0,r))` and `a = s^(n-p)`.  No measure
properties are presumed here; the displayed scaling inequality is explicit.
-/
theorem geometric_mass_lower_bound
    (mass : ℝ → ℝ) (s R a : ℝ)
    (hs : 0 < s) (hR : 0 < R) (ha : 0 ≤ a)
    (hscale : ∀ r : ℝ, 0 < r → a * mass r ≤ mass (s * r))
    (j : ℕ) :
    a ^ j * mass R ≤ mass (s ^ j * R) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      a ^ (j + 1) * mass R = a * (a ^ j * mass R) := by rw [pow_succ]; ring
      _ ≤ a * mass (s ^ j * R) := mul_le_mul_of_nonneg_left ih ha
      _ ≤ mass (s * (s ^ j * R)) :=
        hscale _ (mul_pos (pow_pos hs j) hR)
      _ = mass (s ^ (j + 1) * R) := by congr 1; rw [pow_succ]; ring

/-- A strictly positive initial mass and geometric scaling rule are incompatible
with the corresponding normalized masses tending to zero.

This is the numerical contradiction used in the last lines of
`lem:cone-comparison`; it is not the analytic lemma itself.
-/
theorem no_positive_geometric_density
    (mass : ℝ → ℝ) (s R a : ℝ)
    (hs : 0 < s) (hR : 0 < R) (ha : 0 < a)
    (hpositive : 0 < mass R)
    (hscale : ∀ r : ℝ, 0 < r → a * mass r ≤ mass (s * r))
    (hzero : Tendsto (fun j : ℕ => mass (s ^ j * R) / a ^ j)
      atTop (𝓝 0)) : False := by
  have hlower (j : ℕ) : mass R ≤ mass (s ^ j * R) / a ^ j := by
    apply (le_div_iff₀ (pow_pos ha j)).2
    simpa [mul_comm] using
      geometric_mass_lower_bound mass s R a hs hR ha.le hscale j
  have hnonpos : mass R ≤ 0 :=
    ge_of_tendsto hzero (Eventually.of_forall hlower)
  exact (not_le_of_gt hpositive) hnonpos

/-- Exact real-power normalization at the geometric radii used in the paper. -/
theorem geometric_radius_rpow
    (s R d : ℝ) (hs : 0 < s) (hR : 0 < R) (j : ℕ) :
    (s ^ j * R) ^ d = (s ^ d) ^ j * R ^ d := by
  rw [Real.mul_rpow (pow_nonneg hs.le j) hR.le,
    ← Real.rpow_pow_comm hs.le d j]

/-- The displayed inequality in `eq:cone-iteration`, with the actual
real-power denominator. Set `d = n-p` and `mass r = σ(B(0,r))`.
-/
theorem geometric_rpow_density_lower_bound
    (mass : ℝ → ℝ) (s R d : ℝ)
    (hs : 0 < s) (hR : 0 < R)
    (hscale : ∀ r : ℝ, 0 < r → s ^ d * mass r ≤ mass (s * r))
    (j : ℕ) :
    mass R / R ^ d ≤ mass (s ^ j * R) / (s ^ j * R) ^ d := by
  rw [geometric_radius_rpow s R d hs hR j]
  have ha : 0 < s ^ d := Real.rpow_pos_of_pos hs d
  have hRd : 0 < R ^ d := Real.rpow_pos_of_pos hR d
  apply (div_le_div_iff₀ hRd (mul_pos (pow_pos ha j) hRd)).2
  calc
    mass R * ((s ^ d) ^ j * R ^ d) =
        ((s ^ d) ^ j * mass R) * R ^ d := by ring
    _ ≤ mass (s ^ j * R) * R ^ d :=
      mul_le_mul_of_nonneg_right
        (geometric_mass_lower_bound mass s R (s ^ d) hs hR ha.le hscale j) hRd.le

/-- A positive initial mass and the cone scaling inequality contradict a
vanishing density along the geometric radii. This checks the final algebraic
and limit step of the manuscript's cone-comparison proof.
-/
theorem no_positive_rpow_density
    (mass : ℝ → ℝ) (s R d : ℝ)
    (hs : 0 < s) (hR : 0 < R)
    (hpositive : 0 < mass R)
    (hscale : ∀ r : ℝ, 0 < r → s ^ d * mass r ≤ mass (s * r))
    (hzero : Tendsto (fun j : ℕ => mass (s ^ j * R) / (s ^ j * R) ^ d)
      atTop (𝓝 0)) : False := by
  have hlower (j : ℕ) : mass R / R ^ d ≤
      mass (s ^ j * R) / (s ^ j * R) ^ d :=
    geometric_rpow_density_lower_bound mass s R d hs hR hscale j
  have hnonpos : mass R / R ^ d ≤ 0 :=
    ge_of_tendsto hzero (Eventually.of_forall hlower)
  exact (not_le_of_gt (div_pos hpositive (Real.rpow_pos_of_pos hR d))) hnonpos

/-- Literal radius-limit version of the cone-iteration contradiction.

`hdensity` expresses `mass r = o(r^d)` as `r → 0+`, the content supplied
analytically by `eq:cone-small-density`. Together with the scaling inequality
from `eq:cone-boundary-order`, positive mass at any fixed radius is impossible.
The analytic derivation of these two hypotheses is outside this file.
-/
theorem cone_density_contradiction
    (mass : ℝ → ℝ) (s R d : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hR : 0 < R)
    (hpositive : 0 < mass R)
    (hscale : ∀ r : ℝ, 0 < r → s ^ d * mass r ≤ mass (s * r))
    (hdensity : Tendsto (fun r : ℝ => mass r / r ^ d)
      (𝓝[>] 0) (𝓝 0)) : False := by
  have hradius : Tendsto (fun j : ℕ => s ^ j * R) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs.le hs1).mul_const R
  have hwithin : Tendsto (fun j : ℕ => s ^ j * R) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hradius, Eventually.of_forall ?_⟩
    intro j
    exact mul_pos (pow_pos hs j) hR
  exact no_positive_rpow_density mass s R d hs hR hpositive hscale
    (hdensity.comp hwithin)

#print axioms geometric_mass_lower_bound
#print axioms no_positive_geometric_density
#print axioms geometric_radius_rpow
#print axioms geometric_rpow_density_lower_bound
#print axioms no_positive_rpow_density
#print axioms cone_density_contradiction

end BMCompact
