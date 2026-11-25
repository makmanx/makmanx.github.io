import BallGreenCapacity
import TranslatedBallGreen
import UpstreamBoundaryGreenUnique
import Geometry

/-! The critical outer capacity from eqn2.14 on all closed balls,
including singletons. Both the individual Green capacities and the outer
limit are expressed by their defining properties so uniqueness is explicit. -/
noncomputable section
open Set Metric Filter
open scoped Pointwise Topology
namespace BMCompactPDE

/-- Equation 2.10 in the critical case, with an actual exterior Green function
and a finite asymptotic constant for that function. -/
def HasCriticalGreenCapacity {n : ℕ} (σ : ℝ) (K : Set (Space n)) (c : ℝ) : Prop :=
  ∃ (G : Space n → ℝ) (k : ℝ), IsExteriorGreen n σ n K G ∧
    HasGreenAsymptotic n σ n G k ∧ c = greenCapacityOfConstant n σ n k

/-- Equation 2.14, with convergence through all positive neighbourhood radii. -/
def HasCriticalOuterCapacity {n : ℕ} (σ : ℝ) (K : Set (Space n)) (c : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, (∀ δ, 0 < δ → HasCriticalGreenCapacity σ (BMCompact.closedNeighborhood δ K) (C δ)) ∧
    Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 c)

theorem HasCriticalGreenCapacity.unique {n : ℕ} {σ c d : ℝ} {K : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) (hd : HasCriticalGreenCapacity σ K d) : c = d := by
  rcases hc with ⟨G,k,hG,hk,rfl⟩
  rcases hd with ⟨H,l,hH,hl,rfl⟩
  have hn : 0 < n := by exact_mod_cast (zero_lt_one.trans hG.1)
  rw [hH.unique hG] at hl
  rw [hk.unique_of_dimension hn hl]

theorem HasCriticalOuterCapacity.unique {n : ℕ} {σ c d : ℝ} {K : Set (Space n)}
    (hc : HasCriticalOuterCapacity σ K c) (hd : HasCriticalOuterCapacity σ K d) : c = d := by
  rcases hc with ⟨C,hC,hc⟩
  rcases hd with ⟨D,hD,hd⟩
  have he : C =ᶠ[𝓝[>] (0:ℝ)] D := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hC δ hδ).unique (hD δ hδ)
  exact tendsto_nhds_unique (hc.congr' he) hd

theorem hasCriticalGreenCapacity_closedBall {n : ℕ} {σ r : ℝ}
    (hn : 1 < (n:ℝ)) (hσ : 0 < σ) (hr : 0 < r) (a : Space n) :
    HasCriticalGreenCapacity σ (closedBall a r)
      (Real.exp (1 / σ ^ (-((n:ℝ)-1)⁻¹)) * r) := by
  obtain ⟨G,hG,hk⟩ := exists_translatedBallGreen_with_asymptotic n hσ hn le_rfl hr a
  exact ⟨G,_,hG,hk,(ballGreen_capacity_recipe_critical n hσ hr).symm⟩

/-- The outer capacity of a closed radius-r ball equals exp(1/γ) r, even
when r=0 and the corresponding critical Green function is undefined. -/
theorem hasCriticalOuterCapacity_closedBall {n : ℕ} {σ r : ℝ}
    (hn : 1 < (n:ℝ)) (hσ : 0 < σ) (hr : 0 ≤ r) (a : Space n) :
    HasCriticalOuterCapacity σ (closedBall a r)
      (Real.exp (1 / σ ^ (-((n:ℝ)-1)⁻¹)) * r) := by
  let q := Real.exp (1 / σ ^ (-((n:ℝ)-1)⁻¹))
  refine ⟨fun δ => q * (δ + r), ?_, ?_⟩
  · intro δ hδ
    rw [BMCompact.closedNeighborhood, cthickening_closedBall hδ.le hr]
    exact hasCriticalGreenCapacity_closedBall hn hσ (add_pos_of_pos_of_nonneg hδ hr) a
  · have h := (continuous_const.mul (continuous_id.add continuous_const) :
        Continuous (fun δ : ℝ => q * (δ+r))).continuousAt (x := 0)
    have ht : Tendsto (fun δ : ℝ => q*(δ+r)) (𝓝[>] (0:ℝ)) (𝓝 (q*(0+r))) :=
      h.continuousWithinAt.tendsto
    simpa only [zero_add] using ht

/-- Theorem B(c) is an equality for all pairs of closed balls, also for a
pair involving one or two singletons. No outer-capacity witnesses are inputs. -/
theorem theoremB_critical_outer_ball_equality {n : ℕ} {σ r s t : ℝ}
    (hn : 1 < (n:ℝ)) (hσ : 0 < σ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Space n) :
    ∃ c d : ℝ, HasCriticalOuterCapacity σ (closedBall a r) c ∧
      HasCriticalOuterCapacity σ (closedBall b s) d ∧
      HasCriticalOuterCapacity σ (t • closedBall a r + (1-t) • closedBall b s)
        (t*c + (1-t)*d) := by
  have hu := sub_nonneg.mpr ht1
  refine ⟨_,_,hasCriticalOuterCapacity_closedBall hn hσ hr a,
    hasCriticalOuterCapacity_closedBall hn hσ hs b,?_⟩
  rw [smul_closedBall t a hr, smul_closedBall (1-t) b hs,
    Real.norm_of_nonneg ht, Real.norm_of_nonneg hu,
    closedBall_add_closedBall (mul_nonneg ht hr) (mul_nonneg hu hs)]
  convert hasCriticalOuterCapacity_closedBall hn hσ
    (add_nonneg (mul_nonneg ht hr) (mul_nonneg hu hs)) (t • a + (1-t) • b) using 1
  ring

end BMCompactPDE
#print axioms BMCompactPDE.HasCriticalGreenCapacity.unique
#print axioms BMCompactPDE.HasCriticalOuterCapacity.unique
#print axioms BMCompactPDE.hasCriticalGreenCapacity_closedBall
#print axioms BMCompactPDE.hasCriticalOuterCapacity_closedBall
#print axioms BMCompactPDE.theoremB_critical_outer_ball_equality
