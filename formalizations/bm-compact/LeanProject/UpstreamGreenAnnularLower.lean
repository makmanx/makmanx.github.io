import UpstreamGreenAnnularConstruction

/-! An actual inner-ball lower barrier on the finite annulus. It is deliberately
restricted to the smaller ball: the approximants are constant beyond their
outer radius, so this is not a global lower-profile claim. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem annular_profile_le_radius {n : ℕ} {σ p a : ℝ}
    (hn : 1<(n:ℝ)) (hnp : (n:ℝ)<p) (hσ : 0<σ) (ha : 0<a)
    {x : Space n} (hx : ‖x‖≤a) :
    fundamentalPotential n σ p x≤fundamentalRadialValue n σ p a := by
  let q : ℝ := (p-(n:ℝ))/(p-1)
  have hq : 0<q := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hn.trans hnp))
  simp only [fundamentalRadialValue,fundamentalPotential,if_neg (ne_of_gt hnp),radialPowerPotential,
    Real.norm_eq_abs,abs_of_pos ha]
  change q⁻¹*σ^(-(p-1)⁻¹)*‖x‖^q≤q⁻¹*σ^(-(p-1)⁻¹)*a^q
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hx hq.le)
    (mul_nonneg (inv_nonneg.mpr hq.le) (Real.rpow_nonneg hσ.le _))

set_option maxHeartbeats 1000000 in
theorem WeakPHarmonicPair.fundamental_sub_inner_radius_le_on_ball
    {n : ℕ} {p R a : ℝ} {K : Set (Space n)}
    (hn : 2≤n) (hnp : (n:ℝ)<p) (ha : 0<a)
    (hKa : K⊆closedBall (0 : Space n) a)
    {G : Space n → ℝ} {g : Space n → Space n}
    (hG : WeakPHarmonicPair p (ball 0 R\K) G g)
    (hGc : Continuous G) (hG0 : ∀ x,0≤G x)
    (hGout : ∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) p R) :
    ∀ x∈ball 0 R,fundamentalPotential n (canonicalSphereArea n) p x-
      fundamentalRadialValue n (canonicalSphereArea n) p a≤G x := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hn1 : 1<n := lt_of_lt_of_le (by decide : 1<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast hn1
  have hσ : 0<canonicalSphereArea n := canonicalSphereArea_pos hn0
  let F : Space n → ℝ := fundamentalPotential n (canonicalSphereArea n) p
  let c : ℝ := fundamentalRadialValue n (canonicalSphereArea n) p a
  have hc : 0≤c := by
    have hh := annular_profile_le_radius hnr hnp hσ ha (x:=0) (by simpa using ha.le)
    have hF0 : F 0=0 := by
      have hq : 0<(p-(n:ℝ))/(p-1) := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hnr.trans hnp))
      simp [F,fundamentalPotential,ne_of_gt hnp,radialPowerPotential,Real.zero_rpow (ne_of_gt hq)]
    change F 0≤c at hh
    simpa only [hF0] using hh
  let D : Set (Space n) := ball 0 R\closedBall 0 a
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDb : Bornology.IsBounded D := isBounded_ball.subset sdiff_subset
  have hDG : D⊆ball 0 R\K := fun _ hx=>⟨hx.1,fun hK=>hx.2 (hKa hK)⟩
  have hDF : D⊆{x : Space n | x≠0} := by
    intro x hx hx0
    subst x
    exact hx.2 (by simpa using ha.le)
  have hF : WeakPHarmonicPair p D (fun x=>F x-c) (gradient F) := by
    have hh := ((weakPHarmonicPair_fundamentalPotential n hσ hnr hnp.le).mono hDF hD).add_const (-c)
    simpa only [sub_eq_add_neg] using hh
  have hFc : Continuous (fun x=>F x-c) :=
    (continuous_fundamentalPotential_supercritical n _ hnr hnp).sub continuous_const
  have hboundary : ∀ y∈frontier D,F y-c≤G y := by
    intro y hy
    by_cases hya : y∈closedBall (0 : Space n) a
    · have hh : F y≤c := annular_profile_le_radius hnr hnp hσ ha (by simpa using hya)
      exact (sub_nonpos.mpr hh).trans (hG0 y)
    · have hyn : y∉ball (0 : Space n) R := fun hyB=>(hD.frontier_eq ▸ hy).2 ⟨hyB,hya⟩
      have hyclosed : y∈closedBall (0 : Space n) R := closure_ball_subset_closedBall
        ((closure_mono (sdiff_subset : D⊆ball 0 R)) (frontier_subset_closure hy))
      have hynorm : ‖y‖=R := le_antisymm
        (by simpa only [mem_closedBall,dist_zero_right] using hyclosed)
        (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hyn))
      have hFy : F y=fundamentalRadialValue n (canonicalSphereArea n) p R := by
        change fundamentalPotential n (canonicalSphereArea n) p y=_
        rw [←fundamentalPotential_norm,hynorm]
      rw [hGout y hyn,hFy]
      exact sub_le_self _ hc
  have hcmp := hF.leOn_of_bounded_continuous_boundary_order hn hDb (hG.mono hDG hD)
    hFc.continuousOn hGc.continuousOn hboundary
  intro x hx
  by_cases hxa : x∈closedBall (0 : Space n) a
  · have hh : F x≤c := annular_profile_le_radius hnr hnp hσ ha (by simpa using hxa)
    exact (sub_nonpos.mpr hh).trans (hG0 x)
  · exact hcmp x ⟨hx,hxa⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.fundamental_sub_inner_radius_le_on_ball
