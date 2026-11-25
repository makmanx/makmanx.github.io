import NeighborhoodReflectionOrder
import GreenObstacleOrder
import RadialTranslationLimit

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology EuclideanGeometry AffineSubspace
open scoped Topology Pointwise
namespace BMCompactPDE

private theorem rigid_bounded_remainder {n : ℕ} {p σ : ℝ} (hn : 1<(n:ℝ)) (hpn : (n:ℝ)≤p)
    {G : Space n → ℝ} (hg : HasBoundedGreenRemainder n σ p G) (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    HasBoundedGreenRemainder n σ p (G ∘ e) := by
  let a := e.symm 0
  have he (x : Space n) : ‖e x‖=‖x-a‖ := by
    calc ‖e x‖ = dist (e x) (e a) := by simp [a]
         _ = dist x a := e.dist_map _ _
         _ = ‖x-a‖ := dist_eq_norm _ _
  have hF (x : Space n) : fundamentalPotential n σ p (e x) = fundamentalPotential n σ p (x-a) := by
    simp only [fundamentalPotential,criticalRadialPotential,radialPowerPotential,he]
  obtain ⟨A,hA,hb⟩ := hg
  have hB := e.isometry.antilipschitz.tendsto_cobounded.eventually hb
  have hsmall := (tendsto_fundamentalPotential_translate_sub n σ hn hpn a).abs
  have hs : ∀ᶠ x in cobounded (Space n), |fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x|<1 :=
    hsmall.eventually_lt_const (by norm_num)
  refine ⟨A+1,by linarith,?_⟩
  filter_upwards [hB,hs] with x hx hy
  rw [hF] at hx
  change |G (e x)-fundamentalPotential n σ p x|≤A+1
  rw [show G (e x)-fundamentalPotential n σ p x=(G (e x)-fundamentalPotential n σ p (x-a))+
    (fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x) by ring]
  exact (abs_add_le _ _).trans (add_le_add hx hy.le)

/-- Moving a point farther than the diameter of an enclosing ball can only
increase the exterior Green function. This form isolates the rigid pullback
of the actual weak PDE; no finite asymptotic constant is used. -/
theorem IsExteriorGreen.separated_order_in_enclosing_ball_of_rigid_weak {n : ℕ} {p σ : ℝ} {K : Set (Space n)}
    {G : Space n → ℝ} (hG : IsExteriorGreen n σ p K G)
    (hpull : ∀ e : Space n ≃ᵃⁱ[ℝ] Space n, IsWeakPHarmonic p (e ⁻¹' Kᶜ) (G ∘ e))
    {R : ℝ} (hR : 0<R) (hRK : K ⊆ ball (0:Space n) R) :
    ∀ x y : Space n, ‖x‖+2*R≤‖y‖ → G x≤G y := by
  have hK := hG.2.2.2.1
  have hc := hG.2.2.2.2.2.1
  have hzero := hG.2.2.2.2.2.2.1
  have hnn := hG.nonnegative
  have hInfinity := hG.tendsto_atTop_at_infinity
  have hn1 : 1<n := by exact_mod_cast hG.1
  obtain ⟨g,hg⟩ := hG.2.2.2.2.2.2.2.1
  intro x y hgap
  let S := perpBisector x y
  let e := reflection S
  have hes : e y=x := bisector_reflection_swap x y
  obtain ⟨h,hh⟩ := hpull e
  let H := {w : Space n | dist w y<dist w x}
  let Ω := H ∩ (e ⁻¹' K)ᶜ
  have hop : IsOpen H := isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have hΩ : IsOpen Ω := hop.inter (hK.isClosed.preimage e.continuous).isOpen_compl
  have hsub : H⊆Kᶜ := by
    intro z hz hzK
    have hnorm : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hRK hzK
    have h1 := dist_triangle y z (0:Space n)
    have h2 := dist_triangle z (0:Space n) x
    simp only [dist_zero_right,dist_zero_left,dist_comm y z] at h1 h2
    change dist z y<dist z x at hz
    linarith
  have hdom : Ω⊆e ⁻¹' Kᶜ := inter_subset_right
  have hleft := hh.mono hdom hΩ
  have hright := hg.mono (inter_subset_left.trans hsub) hΩ
  have hxy : y ≠ x := by rintro rfl;linarith
  by_cases hKy : e y∈K
  · rw [←hes,hzero hKy];exact hnn y
  have hyΩ : y∈Ω := ⟨by change dist y y < dist y x;simpa using dist_pos.mpr hxy,hKy⟩
  have hscale (b : ℝ) (hb : 0<b) : G x ≤ (1+b)*G y := by
    have hbd (w : Space n) (hw : w∈frontier Ω) : (G ∘ e) w≤((1+b) • G) w := by
      change G (e w)≤(1+b)*G w
      by_cases h : e w∈K
      · rw [hzero h];exact mul_nonneg (by linarith) (hnn w)
      have hcH : w∈closure H := (closure_mono inter_subset_left) (frontier_subset_closure hw)
      have hle : dist w y≤dist w x := closure_lt_subset_le (continuous_id.dist continuous_const)
        (continuous_id.dist continuous_const) hcH
      have hn : w∉Ω := (hΩ.frontier_eq ▸ hw).2
      have heq : dist w x=dist w y := le_antisymm (le_of_not_gt (fun hlt=>hn ⟨hlt,h⟩)) hle
      have hwS : w∈S := mem_perpBisector_iff_dist_eq.mpr heq
      have hfix : e w=w := (reflection_eq_self_iff w).mpr hwS
      rw [hfix,add_mul,one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hb.le (hnn w))
    obtain ⟨A,_,hA⟩ := hG.2.2.2.2.2.2.2.2
    obtain ⟨B,_,hB⟩ := rigid_bounded_remainder hG.1 hG.2.1 hG.2.2.2.2.2.2.2.2 e
    have hi (ε : ℝ) (hε : 0<ε) : ∀ᶠ w in cocompact (Space n),(G ∘ e) w - ((1+b) • G) w < ε := by
      rw [←Metric.cobounded_eq_cocompact]
      filter_upwards [hA,hB,hInfinity.eventually (eventually_ge_atTop ((A+B)/b))] with w data data' large
      have hlarge := (div_le_iff₀ hb).mp large
      change (G ∘ e) w-(1+b)*G w<ε
      nlinarith only [(abs_le.mp data).1,(abs_le.mp data').2,hlarge,hε]
    have hle := hleft.le_of_frontier_and_decay (by omega) (hright.smul (1+b)) (hc.comp e.continuous)
      (continuous_const.smul hc) hbd hi y hyΩ
    simpa only [Function.comp_apply,hes,Pi.smul_apply,smul_eq_mul] using hle
  have ht : Tendsto (fun b : ℝ=>(1+b)*G y) (𝓝[>] 0) (𝓝 (G y)) := by
    have H : Continuous (fun b : ℝ=>(1+b)*G y) := by fun_prop
    have H' : Tendsto (fun b : ℝ=>(1+b)*G y) (𝓝[>] 0) (𝓝 ((1+(0:ℝ))*G y)) :=
      H.continuousAt.continuousWithinAt
    simpa only [add_zero,one_mul] using H'
  exact ge_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin (fun b hb=>hscale b hb))

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.separated_order_in_enclosing_ball_of_rigid_weak
