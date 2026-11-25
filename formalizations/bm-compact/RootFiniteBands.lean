import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A quantitative finite-band index, selected before any PDE forcing
smallness threshold. The input is genuine finite scalar band data; the
PDE must separately supply its disjointness/energy estimates. -/
set_option autoImplicit false
open Finset
open scoped BigOperators
namespace BMCompactRegularity

theorem finite_band_smallness_index {θ A η : ℝ}
    (hθ : 0<θ) (hA : 0<A) (hη : 0<η) (M : ℝ) :
    ∃ J : ℕ, 0<J ∧ ∀ (Y : ℝ) (b : Fin J → ℝ),
      (∀ j,0≤b j) → (∑ j,b j)≤M →
      (∀ j,Y≤A*(b j)^θ) → Y<η := by
  let a : ℝ := (η/(2*A))^(1/θ)
  have hbase : 0<η/(2*A) := div_pos hη (mul_pos (by norm_num) hA)
  have ha : 0<a := Real.rpow_pos_of_pos hbase _
  have hp : a^θ=η/(2*A) := by
    dsimp only [a]
    rw [←Real.rpow_mul hbase.le,one_div_mul_cancel hθ.ne',Real.rpow_one]
  have hsmall : A*a^θ<η := by
    rw [hp]
    have he : A*(η/(2*A))=η/2 := by field_simp
    rw [he]
    linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (max (M/a) 1)
  have hJpos : 0<J := by
    have h1 : (1:ℝ)<(J:ℝ) := (le_max_right (M/a) 1).trans_lt hJ
    exact_mod_cast (zero_lt_one.trans h1)
  have hJM : M<(J:ℝ)*a := (div_lt_iff₀ ha).mp
    ((le_max_left (M/a) 1).trans_lt hJ)
  refine ⟨J,hJpos,?_⟩
  intro Y b hb hsum hband
  by_contra hnot
  have hηY : η≤Y := le_of_not_gt hnot
  have hbandLower (j : Fin J) : a≤b j := by
    by_contra hj
    have hlt := Real.rpow_lt_rpow (hb j) (lt_of_not_ge hj) hθ
    have hm := mul_lt_mul_of_pos_left hlt hA
    exact (not_lt_of_ge hηY) ((hband j).trans_lt (hm.trans hsmall))
  have hsumLower : (J:ℝ)*a≤∑ j,b j := by
    calc
      (J:ℝ)*a = ∑ _j : Fin J,a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hbandLower j)
  exact (not_lt_of_ge hsum) (hJM.trans_le hsumLower)

end BMCompactRegularity
#print axioms BMCompactRegularity.finite_band_smallness_index
