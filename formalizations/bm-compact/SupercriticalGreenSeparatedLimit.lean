import GreenRemainderEnclosure
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology
open scoped Topology
namespace BMCompactPDE

private theorem sublinear_power_gap {q A D : ℝ} (hq : 0<q) (hq1 : q<1)
    (hA : 0<A) (hD : 0<D) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℝ in atTop, A*(r+D)^q-A*r^q<ε := by
  have hneg : -(1-q)=q-1 := by ring
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hq1)).const_mul (A*D*q)
  rw [hneg,mul_zero] at ht
  filter_upwards [ht.eventually (eventually_lt_nhds hε),eventually_gt_atTop (0:ℝ)] with r hsmall hr
  have hstep : r<r+D := by linarith only [hD]
  obtain ⟨z,hz,hz'⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ=>x^q) (fun x=>q*x^(q-1)) hstep
    ((Real.continuous_rpow_const hq.le).continuousOn)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hr.trans hx.1).ne'))
  change q*z^(q-1)=((r+D)^q-r^q)/((r+D)-r) at hz'
  rw [add_sub_cancel_left] at hz'
  have he := (eq_div_iff hD.ne').mp hz'
  have hb := Real.rpow_le_rpow_of_nonpos hr hz.1.le (sub_nonpos.mpr hq1.le)
  change (A*D*q)*r^(q-1)<ε at hsmall
  calc
    _ = (A*D*q)*z^(q-1) := by rw [←mul_sub,←he]; ring
    _ ≤ (A*D*q)*r^(q-1) := mul_le_mul_of_nonneg_left hb (mul_pos (mul_pos hA hD) hq).le
    _ < ε := hsmall

/-- When the actual supercritical Green function is ordered across a fixed
radial gap, its remainder tends to one finite constant. On the sphere at
r+D the oscillation is bounded by the increment of the sublinear profile. -/
theorem IsExteriorGreen.existsUnique_finite_supercritical_asymptotic_of_separated_order
    {n : ℕ} {σ p : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K G) (hpn : (n:ℝ)<p)
    (hsep : ∃ D : ℝ, 0<D ∧ ∀ x y : Space n, ‖x‖+D≤‖y‖ → G x≤G y) :
    ∃! c : ℝ, HasGreenAsymptotic n σ p G c := by
  obtain ⟨D,hD,horder⟩ := hsep
  have hn := hu.1
  have hnNat : 1<n := by exact_mod_cast hn
  have : NeZero n := ⟨by omega⟩
  have hp := hn.trans hpn
  let q := (p-(n:ℝ))/(p-1)
  let A := q⁻¹*σ^(-(p-1)⁻¹)
  have hq : 0<q := div_pos (sub_pos.mpr hpn) (sub_pos.mpr hp)
  have hq1 : q<1 := (div_lt_one (sub_pos.mpr hp)).mpr (by linarith only [hn])
  have hA : 0<A := mul_pos (inv_pos.mpr hq) (Real.rpow_pos_of_pos hu.2.2.1 _)
  have hprofile (x : Space n) : fundamentalPotential n σ p x=A*‖x‖^q := by
    simp only [fundamentalPotential,if_neg hpn.ne',radialPowerPotential,A,q]
  obtain ⟨B,hKB⟩ := (Metric.isBounded_iff_subset_closedBall (0:Space n)).mp hu.2.2.2.1.isBounded
  have hex : ∃ c : ℝ, HasGreenAsymptotic n σ p G c := by
    apply hu.exists_finite_asymptotic_of_small_enclosing_frontiers
    intro ε hε
    obtain ⟨r,hrB,hr,hsmall⟩ := ((eventually_ge_atTop B).and
      ((eventually_gt_atTop (0:ℝ)).and (sublinear_power_gap hq hq1 hA hD hε))).exists
    have ht : r<r+D := by linarith only [hD]
    have hK : K⊆closedBall (0:Space n) r := hKB.trans (closedBall_subset_closedBall hrB)
    have hne : (sphere (0:Space n) r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have hGc : Continuous G := hu.2.2.2.2.2.1
    obtain ⟨x,hx,hmin⟩ := (isCompact_sphere (0:Space n) r).exists_isMinOn hne hGc.continuousOn
    obtain ⟨y,hy,hmax⟩ := (isCompact_sphere (0:Space n) r).exists_isMaxOn hne hGc.continuousOn
    have hyn : ‖y‖=r := by simpa only [mem_sphere,dist_zero_right] using hy
    have htr := hu.remainder_trapped_by_enclosing_frontier (isCompact_closedBall (0:Space n) r)
      hK hr Subset.rfl (a:=G x-A*r^q) (b:=G y-A*r^q) (by
        intro z hz
        have hzS := frontier_closedBall_subset_sphere hz
        have hzn : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right] using hzS
        rw [hprofile,hzn]
        exact ⟨sub_le_sub_right (hmin hzS) _,sub_le_sub_right (hmax hzS) _⟩)
    refine ⟨closedBall (0:Space n) (r+D),isCompact_closedBall _ _,
      hK.trans (closedBall_subset_closedBall ht.le),⟨r+D,hr.trans ht,Subset.rfl⟩,
      G y-A*(r+D)^q,G y-A*r^q,?_,?_⟩
    · change A*(r+D)^q-A*r^q<ε at hsmall
      linarith only [hsmall]
    intro z hz
    have hzn : ‖z‖=r+D := by simpa only [mem_sphere,dist_zero_right] using (frontier_closedBall_subset_sphere hz)
    have hOut : z∉closedBall (0:Space n) r := by
      simpa only [mem_closedBall,dist_zero_right,not_le,hzn] using ht
    refine ⟨?_,(htr z (fun hi=>hOut (interior_subset hi))).2⟩
    rw [hprofile,hzn]
    exact sub_le_sub_right (horder y z (by rw [hyn,hzn])) _
  obtain ⟨c,hc⟩ := hex
  exact ⟨c,hc,fun d hd=>HasGreenAsymptotic.unique_of_dimension (by omega) hd hc⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.existsUnique_finite_supercritical_asymptotic_of_separated_order
