import CriticalBallComparison
import CriticalBallOuterCapacity

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Pointwise
namespace BMCompactPDE

/-- Capacity given by the actual normalized weak exterior Green function and
its finite asymptotic constant in the manuscript's definition (2.10). -/
def HasFiniteGreenCapacity {n : ℕ} (σ p : ℝ) (K : Set (Space n)) (c : ℝ) : Prop :=
  ∃ (G : Space n → ℝ) (k : ℝ), IsExteriorGreen n σ p K G ∧
    HasGreenAsymptotic n σ p G k ∧ c = greenCapacityOfConstant n σ p k

theorem HasFiniteGreenCapacity.unique {n : ℕ} {σ p c d : ℝ} {K : Set (Space n)}
    (hc : HasFiniteGreenCapacity σ p K c) (hd : HasFiniteGreenCapacity σ p K d) : c = d := by
  obtain ⟨G,k,hG,hk,rfl⟩ := hc
  obtain ⟨H,l,hH,hl,rfl⟩ := hd
  have hn : 0 < n := by exact_mod_cast (zero_lt_one.trans hG.1)
  rw [hH.unique hG] at hl
  rw [hk.unique_of_dimension hn hl]

theorem theoremA_critical_green_closedBalls {n : ℕ} {σ r s t : ℝ}
    (hn : 1 < (n:ℝ)) (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Space n) :
    ∃ c d e : ℝ, HasFiniteGreenCapacity σ n (closedBall a r) c ∧
      HasFiniteGreenCapacity σ n (closedBall b s) d ∧
      HasFiniteGreenCapacity σ n (t • closedBall a r + (1-t) • closedBall b s) e ∧
      e = t*c + (1-t)*d := by
  rw [weighted_closedBalls a b hr.le hs.le ht ht1]
  have hR := weighted_ball_radius_pos hr hs ht ht1
  refine ⟨_,_,_,hasCriticalGreenCapacity_closedBall hn hσ hr a,hasCriticalGreenCapacity_closedBall hn hσ hs b,
    hasCriticalGreenCapacity_closedBall hn hσ hR _,?_⟩
  ring

theorem theoremA_supercritical_green_closedBalls {n : ℕ} {p σ r s t : ℝ}
    (hn : 1 < (n:ℝ)) (hpn : (n:ℝ) < p) (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Space n) :
    ∃ c d e : ℝ, HasFiniteGreenCapacity σ p (closedBall a r) c ∧
      HasFiniteGreenCapacity σ p (closedBall b s) d ∧
      HasFiniteGreenCapacity σ p (t • closedBall a r + (1-t) • closedBall b s) e ∧
      e ^ (1/(p-n)) = t*c^(1/(p-n)) + (1-t)*d^(1/(p-n)) := by
  let A := (((p-(n:ℝ))/(p-1))⁻¹)^(p-1) * σ⁻¹
  let q := p-(n:ℝ)
  have hq : 0 < q := sub_pos.mpr hpn
  have hden : 0 < p-1 := sub_pos.mpr (hn.trans hpn)
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr (div_pos hq hden).le) _) (inv_nonneg.mpr hσ.le)
  have hcap (z : Space n) (R : ℝ) (hR : 0 < R) : HasFiniteGreenCapacity σ p (closedBall z R) (A*R^q) := by
    obtain ⟨G,hG,hk⟩ := exists_translatedBallGreen_with_asymptotic n hσ hn hpn.le hR z
    exact ⟨G,_,hG,hk,(ballGreen_capacity_recipe_supercritical n hn hpn hσ hR).symm⟩
  have hroot (R : ℝ) (hR : 0 < R) : (A*R^q)^(1/q) = A^(1/q)*R := by
    have hmul : q*(1/q) = 1 := by field_simp [hq.ne']
    rw [Real.mul_rpow hA (Real.rpow_nonneg hR.le _),← Real.rpow_mul hR.le,hmul,Real.rpow_one]
  rw [weighted_closedBalls a b hr.le hs.le ht ht1]
  have hR := weighted_ball_radius_pos hr hs ht ht1
  refine ⟨_,_,_,hcap a r hr,hcap b s hs,hcap _ _ hR,?_⟩
  change (A*(t*r+(1-t)*s)^q)^(1/q) = t*(A*r^q)^(1/q) + (1-t)*(A*s^q)^(1/q)
  rw [hroot _ hR,hroot _ hr,hroot _ hs]
  ring

end BMCompactPDE
#print axioms BMCompactPDE.HasFiniteGreenCapacity.unique
#print axioms BMCompactPDE.theoremA_critical_green_closedBalls
#print axioms BMCompactPDE.theoremA_supercritical_green_closedBalls
