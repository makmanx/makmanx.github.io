import UpstreamGreenAnnularComparison
import UpstreamFundamentalSphere
import BallGreenExistence
import BallGreenOrder

/-! Genuine critical lower annular barriers. The globally continuous flattened
ball Green profile avoids any assertion about the raw logarithmic convention
at the pole. The finite-annulus comparison is only on the outer ball. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem WeakPHarmonicPair.ballGreen_lower_bound_on_critical_annulus
    {n : ℕ} {r₀ a R : ℝ} {K : Set (Space n)} (hn : 2≤n)
    (hr₀ : 0<r₀) (hsmall : r₀≤a) (hKa : K⊆closedBall (0 : Space n) a)
    {G : Space n → ℝ} {g : Space n → Space n}
    (hG : WeakPHarmonicPair (n:ℝ) (ball 0 R\K) G g) (hGc : Continuous G)
    (hG0 : ∀ x,0≤G x)
    (hGout : ∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) R-
      fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) r₀) :
    ∀ x∈ball 0 R,ballGreen n (canonicalSphereArea n) (n:ℝ) a x≤G x := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hσ : 0<canonicalSphereArea n := canonicalSphereArea_pos hn0
  have ha : 0<a := hr₀.trans_le hsmall
  let B : Space n → ℝ := ballGreen n (canonicalSphereArea n) (n:ℝ) a
  let D : Set (Space n) := ball 0 R\closedBall 0 a
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDb : Bornology.IsBounded D := isBounded_ball.subset sdiff_subset
  have hDG : D⊆ball 0 R\K := fun _ hx=>⟨hx.1,fun hK=>hx.2 (hKa hK)⟩
  obtain ⟨b,hB⟩ := ballGreen_isWeakPHarmonic n hσ hnr (le_refl (n:ℝ)) ha
  have hBH : WeakPHarmonicPair (n:ℝ) D B b := hB.mono (fun _ hx=>hx.2) hD
  have hBc : Continuous B := continuous_ballGreen n _ _ ha
  have hFa : fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) r₀≤
      fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) a :=
    fundamentalRadialValue_mono_positive n hnr le_rfl hσ hr₀ hsmall
  have hboundary : ∀ y∈frontier D,B y≤G y := by
    intro y hy
    by_cases hya : y∈closedBall (0 : Space n) a
    · have hzero : B y=0 := ballGreen_eq_zero_of_norm_le n _ _ a (by simpa using hya)
      rw [hzero]
      exact hG0 y
    · have hyn : y∉ball (0 : Space n) R := fun hyB=>(hD.frontier_eq ▸ hy).2 ⟨hyB,hya⟩
      have hyclosed : y∈closedBall (0 : Space n) R := closure_ball_subset_closedBall
        ((closure_mono (sdiff_subset : D⊆ball 0 R)) (frontier_subset_closure hy))
      have hynorm : ‖y‖=R := le_antisymm
        (by simpa only [mem_closedBall,dist_zero_right] using hyclosed)
        (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hyn))
      have hyaNorm : a≤‖y‖ := (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hya)).le
      have hBy : B y=fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) R-
          fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) a := by
        change ballGreen n (canonicalSphereArea n) (n:ℝ) a y=_
        rw [ballGreen_eq_profile_sub_of_le_norm n _ _ a hyaNorm,←fundamentalPotential_norm,hynorm]
      rw [hBy,hGout y hyn]
      exact sub_le_sub_left hFa _
  have hcmp := hBH.leOn_of_bounded_continuous_boundary_order hn hDb (hG.mono hDG hD)
    hBc.continuousOn hGc.continuousOn hboundary
  intro x hx
  by_cases hxa : x∈closedBall (0 : Space n) a
  · rw [ballGreen_eq_zero_of_norm_le n _ _ a (by simpa using hxa)]
    exact hG0 x
  · exact hcmp x ⟨hx,hxa⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.ballGreen_lower_bound_on_critical_annulus
