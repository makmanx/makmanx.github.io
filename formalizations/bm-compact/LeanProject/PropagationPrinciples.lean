import PropagationAnnular
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Six strong-minimum and Hopf proof bodies composed once from two file scopes.
Readable segments are provenance, not additional build targets or counts. -/
section PropagationStrongMinimumScope

/-! The actual strong minimum principle for continuous weak p-supersolutions
on arbitrary preconnected open Euclidean domains. Annular comparison propagates
strict positivity; no Harnack, C1 regularity or maximum principle is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

/-- A nonnegative continuous weak supersolution which is positive somewhere
is positive throughout a preconnected domain. -/
theorem WeakPSupersolutionPair.positive_of_nonneg_of_positive_somewhere
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hc : ContinuousOn u Ω)
    (hconn : IsPreconnected Ω) (h0 : ∀ x ∈ Ω, 0 ≤ u x)
    (hpos : ∃ x ∈ Ω, 0 < u x) : ∀ x ∈ Ω, 0 < u x := by
  let P : Set (Space n) := Ω ∩ u ⁻¹' Ioi 0
  have hPo : IsOpen P := hc.isOpen_inter_preimage hu.2.1 isOpen_Ioi
  have hsome : (Ω ∩ P).Nonempty := by
    obtain ⟨x,hx,hux⟩ := hpos
    exact ⟨x,hx,hx,hux⟩
  have hclosed : closure P ∩ Ω ⊆ P := by
    intro x hx
    by_cases hxp : x ∈ P
    · exact hxp
    obtain ⟨η,hη,hηΩ⟩ := Metric.isOpen_iff.mp hu.2.1 x hx.2
    let ρ : ℝ := η/4
    have hρ : 0 < ρ := div_pos hη (by norm_num)
    obtain ⟨a,ha,hxa⟩ := Metric.mem_closure_iff.mp hx.1 ρ hρ
    have haΩ : a ∈ Ω := ha.1
    have hua : 0 < u a := ha.2
    have hax : dist a x < ρ := by simpa only [dist_comm] using hxa
    have hne : x ≠ a := by
      intro he
      subst a
      exact hxp ha
    have hd : 0 < dist x a := dist_pos.mpr hne
    let m : ℝ := u a/2
    have hm : 0 < m := half_pos hua
    have hma : m < u a := half_lt_self hua
    have huc := hc.continuousAt (hu.2.1.mem_nhds haΩ)
    have hN : {z : Space n | m < u z} ∈ 𝓝 a :=
      huc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hma)
    obtain ⟨ε,hε,hεu⟩ := Metric.mem_nhds_iff.mp hN
    let r : ℝ := min (ε/2) (dist x a/2)
    have hr : 0 < r := lt_min (half_pos hε) (half_pos hd)
    have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hrd : r < dist x a := (min_le_right _ _).trans_lt (half_lt_self hd)
    have hρ2 : ρ < 2*ρ := by linarith
    have hrR : r < 2*ρ := hrd.trans (hxa.trans hρ2)
    have hball : closedBall a (2*ρ) ⊆ Ω := by
      intro z hz
      apply hηΩ
      have hza : dist z a ≤ 2*ρ := mem_closedBall.mp hz
      have hzx : dist z x < η := by
        calc
          dist z x ≤ dist z a + dist a x := dist_triangle z a x
          _ < 2*ρ+ρ := add_lt_add_of_le_of_lt hza hax
          _ < η := by dsimp only [ρ]; linarith
      exact hzx
    have hcl : closure (radialAnnulusAt n a r (2*ρ)) ⊆ Ω := by
      intro z hz
      exact hball ((bounds_of_mem_closure_radialAnnulusAt n a r (2*ρ) hz).2)
    have hAnn := hu.mono (subset_closure.trans hcl) (isOpen_radialAnnulusAt n a r (2*ρ))
    have hinner : ∀ z : Space n, dist z a = r → m ≤ u z := by
      intro z hz
      exact (hεu (by simpa only [mem_ball,hz] using hrε)).le
    have houter : ∀ z : Space n, dist z a = 2*ρ → 0 ≤ u z := by
      intro z hz
      exact h0 z (hball (by simpa only [mem_closedBall,hz] using (le_rfl : 2*ρ ≤ 2*ρ)))
    have hxAnn : x ∈ radialAnnulusAt n a r (2*ρ) := ⟨hrd,hxa.trans hρ2⟩
    have hux := annular_positive_of_continuous_weak_supersolution hn hu.1 hr hrR hm a
      hAnn (hc.mono hcl) hinner houter x hxAnn
    exact ⟨hx.2,hux⟩
  have hΩP := hconn.subset_of_closure_inter_subset hPo hsome hclosed
  intro x hx
  exact (hΩP hx).2

/-- A nonnegative continuous weak supersolution attaining zero inside a
preconnected domain vanishes throughout that domain. -/
theorem WeakPSupersolutionPair.eq_zero_of_nonneg_of_zero
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hc : ContinuousOn u Ω)
    (hconn : IsPreconnected Ω) (h0 : ∀ x ∈ Ω, 0 ≤ u x)
    {a : Space n} (ha : a ∈ Ω) (hzero : u a = 0) : ∀ x ∈ Ω, u x = 0 := by
  intro x hx
  by_contra hne
  have hxp : 0 < u x := lt_of_le_of_ne (h0 x hx) (Ne.symm hne)
  have hap := hu.positive_of_nonneg_of_positive_somewhere hn hc hconn h0 ⟨x,hx,hxp⟩ a ha
  simpa only [hzero,lt_self_iff_false] using hap

/-- In particular, the strong minimum principle applies to the actual
existential weak p-harmonic predicate and its selected continuous representative. -/
theorem IsWeakPHarmonic.eq_zero_of_nonneg_of_zero
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (hc : ContinuousOn u Ω)
    (hconn : IsPreconnected Ω) (h0 : ∀ x ∈ Ω, 0 ≤ u x)
    {a : Space n} (ha : a ∈ Ω) (hzero : u a = 0) : ∀ x ∈ Ω, u x = 0 := by
  obtain ⟨g,hg⟩ := hu
  exact hg.supersolution.eq_zero_of_nonneg_of_zero hn hc hconn h0 ha hzero

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSupersolutionPair.positive_of_nonneg_of_positive_somewhere
#print axioms BMCompactPDE.WeakPSupersolutionPair.eq_zero_of_nonneg_of_zero
#print axioms BMCompactPDE.IsWeakPHarmonic.eq_zero_of_nonneg_of_zero
end
end PropagationStrongMinimumScope

section PropagationHopfScope

/-! Derivative-free Hopf growth for actual continuous weak supersolutions.
The actual annular comparison constructs the positive linear lower bound.
A boundary gradient is used only in the last corollary, at that single point. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

/-- Annular positive inner data give actual one-sided linear growth at every
outer-sphere point. The weak supersolution need not have any classical derivative. -/
theorem annular_hopf_linear_bound_of_continuous_weak_supersolution
    {n : ℕ} (hn : 2 ≤ n) {p r R m : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m) (a : Space n)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p (radialAnnulusAt n a r R) u g)
    (hc : ContinuousOn u (closure (radialAnnulusAt n a r R)))
    (hinner : ∀ x : Space n, dist x a = r → m ≤ u x)
    (houter : ∀ x : Space n, dist x a = R → 0 ≤ u x)
    {ν : Space n} (hν : ‖ν‖ = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      c*s ≤ u (a+(R • ν-s • ν)) := by
  have hR : 0 < R := hr.trans hrR
  let C : ℝ := m * ((R ^ ((p-(n : ℝ))/(p-1)-2)*R) /
    annularBarrierDenominator n p r R)
  have hC : 0 < C := mul_pos hm
    (div_pos (mul_pos (Real.rpow_pos_of_pos hR _) hR)
      (annularBarrierDenominator_pos n hp hr hrR))
  let f : ℝ → ℝ := fun s => m * annularRadialBarrier n p r R (R • ν-s • ν)
  have hf : HasDerivAt f C 0 :=
    (inward_derivative_annularRadialBarrier n (r := r) hp hR hν).const_mul m
  have hnR : ‖R • ν‖ = R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hν,mul_one]
  have hf0 : f 0 = 0 := by
    simp only [f,zero_smul,sub_zero,annularRadialBarrier_zero_outer n p r R hnR,mul_zero]
  have hlim : Tendsto (fun s : ℝ => f s/s) (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [zero_add,hf0,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hf.tendsto_slope_zero_right
  have hhalf : C/2 < C := half_lt_self hC
  have hsl := hlim.eventually (eventually_gt_nhds hhalf)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < R-r :=
    (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
  have hlow := annularRadialBarrier_le_of_continuous_weak_supersolution
    hn hp hr hrR a hu hc hinner houter
  refine ⟨C/2,half_pos hC,?_⟩
  filter_upwards [hsl,hsmall,self_mem_nhdsWithin] with s hs hsR hs0
  have hsp : 0 < s := hs0
  have hnorm : ‖R • ν-s • ν‖ = R-s := by
    rw [←sub_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith),hν,mul_one]
  have hshift : (a+(R • ν-s • ν))-a = R • ν-s • ν := by abel
  have hxA : a+(R • ν-s • ν) ∈ radialAnnulusAt n a r R := by
    change r < dist (a+(R • ν-s • ν)) a ∧ dist (a+(R • ν-s • ν)) a < R
    rw [dist_eq_norm,hshift,hnorm]
    constructor <;> linarith
  have hb := hlow (a+(R • ν-s • ν)) hxA
  rw [hshift] at hb
  have hcs : (C/2)*s ≤ f s := ((lt_div_iff₀ hsp).mp hs).le
  exact hcs.trans hb

/-- A nontrivial nonnegative continuous weak supersolution on a ball has
positive inward linear growth at each zero boundary point. Strong interior
positivity is derived from the actual strong minimum principle, not assumed. -/
theorem WeakPSupersolutionPair.ball_hopf_linear_bound
    {n : ℕ} (hn : 2 ≤ n) {p R : ℝ} (hR : 0 < R) (a : Space n)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p (ball a R) u g)
    (hc : ContinuousOn u (closure (ball a R)))
    (h0 : ∀ x ∈ ball a R, 0 ≤ u x) (hpos : ∃ x ∈ ball a R, 0 < u x)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (a+R • ν) = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      c*s ≤ u (a+(R • ν-s • ν))-u (a+R • ν) := by
  have hpositive := hu.positive_of_nonneg_of_positive_somewhere hn
    (hc.mono subset_closure) (convex_ball a R).isPreconnected h0 hpos
  let r : ℝ := R/2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := half_lt_self hR
  have hSr : sphere a r ⊆ ball a R := by
    intro x hx
    exact (mem_sphere.mp hx).trans_lt hrR
  have hne : (sphere a r).Nonempty := by
    refine ⟨a+r • ν,?_⟩
    rw [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr,hν,mul_one]
  obtain ⟨y,hy,hmin⟩ := (isCompact_sphere a r).exists_isMinOn hne
    (hc.mono (hSr.trans subset_closure))
  have hm : 0 < u y := hpositive y (hSr hy)
  have hinner : ∀ x : Space n, dist x a = r → u y ≤ u x := by
    intro x hx
    exact hmin (mem_sphere.mpr hx)
  have houter : ∀ x : Space n, dist x a = R → 0 ≤ u x := by
    intro x hx
    apply le_on_closure h0 continuousOn_const hc
    rw [closure_ball a hR.ne']
    exact hx.le
  have hAsub : radialAnnulusAt n a r R ⊆ ball a R := fun _ hx => hx.2
  have hAnn := hu.mono hAsub (isOpen_radialAnnulusAt n a r R)
  obtain ⟨c,hc0,hcl⟩ := annular_hopf_linear_bound_of_continuous_weak_supersolution
    hn hu.1 hr hrR hm a hAnn (hc.mono (closure_mono hAsub)) hinner houter hν
  refine ⟨c,hc0,?_⟩
  simpa only [hzero,sub_zero] using hcl

/-- Whenever a genuine boundary gradient exists, the continuous weak-ball
Hopf growth forces its inward component to be positive. No C1 extension of u
or classical differentiability inside the ball is assumed. -/
theorem WeakPSupersolutionPair.ball_hopf_of_hasGradientAt
    {n : ℕ} (hn : 2 ≤ n) {p R : ℝ} (hR : 0 < R) (a : Space n)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p (ball a R) u g)
    (hc : ContinuousOn u (closure (ball a R)))
    (h0 : ∀ x ∈ ball a R, 0 ≤ u x) (hpos : ∃ x ∈ ball a R, 0 < u x)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (a+R • ν) = 0)
    {G : Space n} (hG : HasGradientAt u G (a+R • ν)) :
    0 < ⟪G,-ν⟫_ℝ ∧ G ≠ 0 := by
  obtain ⟨c,hc0,hcl⟩ := hu.ball_hopf_linear_bound hn hR a hc h0 hpos hν hzero
  have hpath : HasDerivAt (fun s : ℝ => a+(R • ν-s • ν)) (-ν) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub (R • ν)).const_add a
  have hdu := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hdu' : HasDerivAt (fun s : ℝ => u (a+(R • ν-s • ν))) ⟪G,-ν⟫_ℝ 0 := by
    simpa only [Function.comp_apply,toDual_apply_apply] using! hdu
  have hdc : HasDerivAt (fun s : ℝ => c*s+u (a+R • ν)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).add_const (u (a+R • ν))
  have hle : c ≤ ⟪G,-ν⟫_ℝ := by
    apply derivative_le_of_eventually_le_right hdc hdu'
    · simp
    · filter_upwards [hcl] with s hs
      linarith
  have hp := hc0.trans_le hle
  refine ⟨hp,?_⟩
  intro he
  simpa only [he,inner_zero_left,lt_self_iff_false] using hp

end BMCompactPDE
#print axioms BMCompactPDE.annular_hopf_linear_bound_of_continuous_weak_supersolution
#print axioms BMCompactPDE.WeakPSupersolutionPair.ball_hopf_linear_bound
#print axioms BMCompactPDE.WeakPSupersolutionPair.ball_hopf_of_hasGradientAt
end
end PropagationHopfScope
