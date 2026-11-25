import GreenObstacleOrder
import UpstreamGreenAnnularComparison
import BallGreenExistence
import BallGreenOrder

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology
open scoped Topology
namespace BMCompactPDE

/-- Two bounds on the remainder along one compact enclosing boundary hold
everywhere beyond the enclosure. The enclosure can for example be a cube. -/
theorem IsExteriorGreen.remainder_trapped_by_enclosing_frontier
    {n : ℕ} {p σ : ℝ} {K E : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) (hE : IsCompact E) (hKE : K⊆E)
    {r : ℝ} (hr : 0<r) (hinner : closedBall (0:Space n) r⊆E)
    {a b : ℝ} (hfront : ∀ x∈frontier E, a≤u x-fundamentalPotential n σ p x ∧
      u x-fundamentalPotential n σ p x≤b) :
    ∀ x∉interior E, a≤u x-fundamentalPotential n σ p x ∧
      u x-fundamentalPotential n σ p x≤b := by
  obtain ⟨hn,hp,hσ,_,_,huc,_,⟨g,hH⟩,A,_,hA⟩ := hu
  have hnNat : 1 < n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  let B := ballGreen n σ p r
  let f := fundamentalPotential n σ p (E:=Space n)
  let c := fundamentalRadialValue n σ p r
  have hBc : Continuous B := continuous_ballGreen _ _ _ hr
  have hB0 (x : Space n) : 0 ≤ B x := ballGreen_nonneg n hn hp hσ hr x
  obtain ⟨gB,hBH⟩ := ballGreen_isWeakPHarmonic n hσ hn hp hr
  have hball : ball (0:Space n) r ⊆ interior E :=
    isOpen_ball.subset_interior_iff.mpr (ball_subset_closedBall.trans hinner)
  have hBx (x : Space n) (hx : x∉interior E) : B x = f x-c := by
    apply ballGreen_eq_profile_sub_of_le_norm
    exact le_of_not_gt (fun h=>hx (hball (by simpa only [mem_ball,dist_zero_right] using h)))
  have hlarge : Tendsto B (cobounded (Space n)) atTop :=
    (ballGreen_isExteriorGreen n hσ hn hp hr).tendsto_atTop_at_infinity
  intro x hx
  by_cases hxE : x∈E
  · exact hfront x ⟨subset_closure hxE,hx⟩
  have hpert (δ : ℝ) (hδ : 0<δ) :
      f x+a-δ*B x ≤ u x ∧ u x ≤ f x+b+δ*B x := by
    let L := fun z => ((1-δ) • B) z + (c+a)
    let U := fun z => ((1+δ) • B) z + (c+b)
    have hout : ∀ᶠ z : Space n in cobounded (Space n), z∉E ∧ L z ≤ u z ∧ u z ≤ U z := by
      filter_upwards [hE.isBounded.compl,hA,hlarge.eventually
        (eventually_ge_atTop ((A+|a|+|b|)/δ))] with z hz ha hbig
      have hzf := hBx z (fun hi => hz (interior_subset hi))
      change |u z-f z| ≤ A at ha
      have hδB := (div_le_iff₀ hδ).mp hbig
      refine ⟨hz,?_⟩
      change (1-δ)*B z+(c+a) ≤ u z ∧ u z ≤ (1+δ)*B z+(c+b)
      constructor <;> nlinarith only [(abs_le.mp ha).1,(abs_le.mp ha).2,hzf,hδB,
        le_abs_self a,neg_le_abs b,abs_nonneg a,abs_nonneg b]
    obtain ⟨t,_,ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hout
    let Q := max t ‖x‖+1
    let D := ball (0:Space n) Q \ E
    have hD : IsOpen D := isOpen_ball.sdiff hE.isClosed
    have hDb : Bornology.IsBounded D := isBounded_ball.subset sdiff_subset
    have hdx : x∈D := by
      refine ⟨?_,hxE⟩
      change dist x 0 < Q
      rw [dist_zero_right]
      dsimp [Q]; linarith only [le_max_right t ‖x‖]
    have hdu := hH.mono (show D⊆Kᶜ from fun _ hy hyK => hy.2 (hKE hyK)) hD
    have hdb := hBH.mono (show D⊆(closedBall (0:Space n) r)ᶜ from
      fun _ hy hyB=>hy.2 (hinner hyB)) hD
    have hboundary (y : Space n) (hy : y∈frontier D) : L y ≤ u y ∧ u y ≤ U y := by
      by_cases hyE : y∈E
      · have hcomp : D⊆Eᶜ := fun _ h => h.2
        have hno : y∉interior E := by
          have hh := closure_mono hcomp (frontier_subset_closure hy)
          simpa only [closure_compl,mem_compl_iff] using hh
        have hh := hfront y ⟨subset_closure hyE,hno⟩
        have hf := hBx y hno
        change a ≤ u y-f y ∧ u y-f y ≤ b at hh
        have hδB := mul_nonneg hδ.le (hB0 y)
        change (1-δ)*B y+(c+a) ≤ u y ∧ u y ≤ (1+δ)*B y+(c+b)
        constructor <;> nlinarith only [hh.1,hh.2,hf,hδB]
      · have hno : y∉ball (0:Space n) Q := fun hyB=>(hD.frontier_eq ▸ hy).2 ⟨hyB,hyE⟩
        have hnorm : Q≤‖y‖ := le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hno)
        exact (ht (show t≤‖y‖ by dsimp only [Q] at hnorm;linarith only [hnorm,le_max_left t ‖x‖])).2
    have hlow := ((hdb.smul (1-δ)).add_const (c+a)).leOn_of_bounded_continuous_boundary_order
      hn2 hDb hdu ((continuous_const.smul hBc).add continuous_const).continuousOn huc.continuousOn
      (fun y hy=>(hboundary y hy).1) x hdx
    have hhi := hdu.leOn_of_bounded_continuous_boundary_order hn2 hDb
      ((hdb.smul (1+δ)).add_const (c+b)) huc.continuousOn
      ((continuous_const.smul hBc).add continuous_const).continuousOn (fun y hy=>(hboundary y hy).2) x hdx
    change (1-δ)*B x+(c+a) ≤ u x at hlow
    change u x ≤ (1+δ)*B x+(c+b) at hhi
    constructor <;> nlinarith only [hlow,hhi,hBx x hx]
  let δ := fun j : ℕ => ((j:ℝ)+1)⁻¹
  have hδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have hδ0 (j : ℕ) : 0 < δ j := inv_pos.mpr (by positivity)
  have hl : f x+a ≤ u x := by
    have ht : Tendsto (fun j => f x+a-δ j*B x) atTop (𝓝 (f x+a)) := by
      simpa only [zero_mul,sub_zero] using
        (tendsto_const_nhds (x:=f x+a) (f:=atTop (α:=ℕ))).sub (hδ.mul_const (B x))
    exact le_of_tendsto ht (Eventually.of_forall (fun j=>(hpert _ (hδ0 j)).1))
  have hh : u x ≤ f x+b := by
    have ht : Tendsto (fun j => f x+b+δ j*B x) atTop (𝓝 (f x+b)) := by
      simpa only [zero_mul,add_zero] using
        (tendsto_const_nhds (x:=f x+b) (f:=atTop (α:=ℕ))).add (hδ.mul_const (B x))
    exact ge_of_tendsto ht (Eventually.of_forall (fun j=>(hpert _ (hδ0 j)).2))
  change a ≤ u x-f x ∧ u x-f x ≤ b
  constructor <;> linarith only [hl,hh]

/-- Finite asymptotics follow if arbitrarily narrow remainder intervals occur
on individual enclosing boundaries. No convergence, common center for those
intervals, or control on the rest of the exterior is an input. -/
theorem IsExteriorGreen.exists_finite_asymptotic_of_small_enclosing_frontiers
    {n : ℕ} {p σ : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u)
    (hosc : ∀ ε : ℝ, 0<ε → ∃ E : Set (Space n), IsCompact E ∧ K⊆E ∧
      (∃ r : ℝ, 0<r ∧ closedBall (0:Space n) r ⊆ E) ∧
      ∃ a b : ℝ, b-a<ε ∧ ∀ x∈frontier E,
        a≤u x-fundamentalPotential n σ p x ∧ u x-fundamentalPotential n σ p x≤b) :
    ∃ c : ℝ, HasGreenAsymptotic n σ p u c := by
  have hn : 1<n := by exact_mod_cast hu.1
  have : NeZero n := ⟨by omega⟩
  let k := fun x => u x-fundamentalPotential n σ p x
  have hC : Cauchy (map k (cobounded (Space n))) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance,?_⟩
    intro ε hε
    obtain ⟨E,hE,hKE,⟨r,hr,hrE⟩,a,b,hab,hbound⟩ := hosc ε hε
    have ht := hu.remainder_trapped_by_enclosing_frontier hE hKE hr hrE hbound
    refine ⟨Icc a b,?_,?_⟩
    · change {x : Space n | k x ∈ Icc a b} ∈ cobounded (Space n)
      filter_upwards [hE.isBounded.compl] with x hx
      exact ht x (fun h=>hx (interior_subset h))
    · intro x hx y hy
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith only [hx.1,hy.2,hab],by linarith only [hx.2,hy.1,hab]⟩
  exact cauchy_iff_exists_le_nhds.mp hC

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.remainder_trapped_by_enclosing_frontier
#print axioms BMCompactPDE.IsExteriorGreen.exists_finite_asymptotic_of_small_enclosing_frontiers
