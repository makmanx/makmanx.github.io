import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The actual geometric source floor in the spatial C0 iteration. These are
pure scalar inequalities/limits. No PDE or continuity-of-solution premise is
introduced. Authored by the exterior specialist for root's C0 integration. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace BMCompactRegularity

theorem source_floor_of_not_small {p R eps w c : ℝ}
    (hp : 1<p) (hR : 0<R) (heps : 0<eps) (hw : 0≤w)
    (hnot : ¬R^p*|c|≤eps*w^(p-1)) :
    w≤(|c|/eps)^(1/(p-1))*R^(p/(p-1)) := by
  have ha : 0<p-1 := sub_pos.mpr hp
  have hbase : 0≤|c|/eps := div_nonneg (abs_nonneg _) heps.le
  let B : ℝ := (|c|/eps)^(1/(p-1))*R^(p/(p-1))
  have hB : 0≤B := mul_nonneg (Real.rpow_nonneg hbase _) (Real.rpow_nonneg hR.le _)
  have hpower : B^(p-1)=(|c|/eps)*R^p := by
    dsimp only [B]
    rw [Real.mul_rpow (Real.rpow_nonneg hbase _) (Real.rpow_nonneg hR.le _),
      ←Real.rpow_mul hbase, ←Real.rpow_mul hR.le]
    have hleft : (1/(p-1))*(p-1)=1 := div_mul_cancel₀ 1 ha.ne'
    have hright : (p/(p-1))*(p-1)=p := div_mul_cancel₀ p ha.ne'
    rw [hleft, hright, Real.rpow_one]
  apply (Real.rpow_le_rpow_iff hw hB ha).mp
  rw [hpower]
  have hstrict : eps*w^(p-1)<R^p*|c| := lt_of_not_ge hnot
  have hdiv : w^(p-1)<(R^p*|c|)/eps :=
    (lt_div_iff₀ heps).mpr (by simpa only [mul_comm] using hstrict)
  exact hdiv.le.trans_eq (by ring)

theorem tendsto_geometric_source_floor {p R0 t : ℝ}
    (hp : 1<p) (_hR0 : 0<R0) (ht0 : 0≤t) (ht1 : t<1) (eps c : ℝ) :
    Tendsto (fun j : ℕ => (|c|/eps)^(1/(p-1))*(R0*t^j)^(p/(p-1)))
      atTop (𝓝 0) := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hpower : 0<p/(p-1) := div_pos hp0 (sub_pos.mpr hp)
  have hbase : Tendsto (fun j : ℕ => R0*t^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul R0
  have hlim := (hbase.rpow_const (Or.inr hpower.le)).const_mul ((|c|/eps)^(1/(p-1)))
  simpa only [Real.zero_rpow hpower.ne', mul_zero] using hlim

end BMCompactRegularity
#print axioms BMCompactRegularity.source_floor_of_not_small
#print axioms BMCompactRegularity.tendsto_geometric_source_floor
