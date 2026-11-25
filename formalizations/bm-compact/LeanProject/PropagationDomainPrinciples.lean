import PropagationPrinciples

/-! General-domain Hopf under an actual interior-ball condition, and strong
maximum/minimum consequences for the actual p-harmonic predicate. Geometry,
continuity and any single-point gradient are stated explicitly. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem WeakPSupersolutionPair.hopf_linear_bound_of_interior_ball
    {n : ℕ} (hn : 2 ≤ n) {p R : ℝ} {Ω : Set (Space n)}
    (hR : 0 < R) (a : Space n) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hc : ContinuousOn u (closure Ω))
    (hconn : IsPreconnected Ω) (h0 : ∀ x ∈ Ω, 0 ≤ u x)
    (hpos : ∃ x ∈ Ω, 0 < u x) (hball : ball a R ⊆ Ω)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (a+R • ν) = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      c*s ≤ u (a+(R • ν-s • ν))-u (a+R • ν) := by
  have hpositive := hu.positive_of_nonneg_of_positive_somewhere hn
    (hc.mono subset_closure) hconn h0 hpos
  have ha : a ∈ ball a R := mem_ball_self hR
  exact (hu.mono hball isOpen_ball).ball_hopf_linear_bound hn hR a
    (hc.mono (closure_mono hball)) (fun x hx => h0 x (hball hx))
    ⟨a,ha,hpositive a (hball ha)⟩ hν hzero

theorem WeakPSupersolutionPair.hopf_of_interior_ball_of_hasGradientAt
    {n : ℕ} (hn : 2 ≤ n) {p R : ℝ} {Ω : Set (Space n)}
    (hR : 0 < R) (a : Space n) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hc : ContinuousOn u (closure Ω))
    (hconn : IsPreconnected Ω) (h0 : ∀ x ∈ Ω, 0 ≤ u x)
    (hpos : ∃ x ∈ Ω, 0 < u x) (hball : ball a R ⊆ Ω)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (a+R • ν) = 0)
    {G : Space n} (hG : HasGradientAt u G (a+R • ν)) :
    0 < ⟪G,-ν⟫_ℝ ∧ G ≠ 0 := by
  have hpositive := hu.positive_of_nonneg_of_positive_somewhere hn
    (hc.mono subset_closure) hconn h0 hpos
  have ha : a ∈ ball a R := mem_ball_self hR
  exact (hu.mono hball isOpen_ball).ball_hopf_of_hasGradientAt hn hR a
    (hc.mono (closure_mono hball)) (fun x hx => h0 x (hball hx))
    ⟨a,ha,hpositive a (hball ha)⟩ hν hzero hG

/-- An attained lower bound forces an actual continuous weak p-harmonic
function to be constant on a preconnected domain. -/
theorem IsWeakPHarmonic.eq_const_of_le_of_eq
    {n : ℕ} (hn : 2 ≤ n) {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (hc : ContinuousOn u Ω)
    (hconn : IsPreconnected Ω) (hbound : ∀ x ∈ Ω, c ≤ u x)
    {a : Space n} (ha : a ∈ Ω) (heq : u a = c) : ∀ x ∈ Ω, u x = c := by
  have hw := hu.sub_const c
  have hwc : ContinuousOn (fun x => u x-c) Ω := hc.sub continuousOn_const
  have hw0 : ∀ x ∈ Ω, 0 ≤ u x-c := fun x hx => sub_nonneg.mpr (hbound x hx)
  have hwa : u a-c=0 := by rw [heq,sub_self]
  have hz := hw.eq_zero_of_nonneg_of_zero hn hwc hconn hw0 ha hwa
  intro x hx
  exact sub_eq_zero.mp (hz x hx)

/-- The actual strong maximum principle, from a genuine scalar sign change
of the weak equation and the proved continuous strong minimum principle. -/
theorem IsWeakPHarmonic.eq_const_of_ge_of_eq
    {n : ℕ} (hn : 2 ≤ n) {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (hc : ContinuousOn u Ω)
    (hconn : IsPreconnected Ω) (hbound : ∀ x ∈ Ω, u x ≤ c)
    {a : Space n} (ha : a ∈ Ω) (heq : u a = c) : ∀ x ∈ Ω, u x = c := by
  have hw : IsWeakPHarmonic p Ω (fun x => c-u x) := by
    apply ((hu.smul (-1)).add_const c).congr_on
    intro x hx
    simp only [Pi.smul_apply,smul_eq_mul,neg_one_mul]
    ring
  have hwc : ContinuousOn (fun x => c-u x) Ω := continuousOn_const.sub hc
  have hw0 : ∀ x ∈ Ω, 0 ≤ c-u x := fun x hx => sub_nonneg.mpr (hbound x hx)
  have hwa : c-u a=0 := by rw [heq,sub_self]
  have hz := hw.eq_zero_of_nonneg_of_zero hn hwc hconn hw0 ha hwa
  intro x hx
  exact (sub_eq_zero.mp (hz x hx)).symm

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSupersolutionPair.hopf_linear_bound_of_interior_ball
#print axioms BMCompactPDE.WeakPSupersolutionPair.hopf_of_interior_ball_of_hasGradientAt
#print axioms BMCompactPDE.IsWeakPHarmonic.eq_const_of_le_of_eq
#print axioms BMCompactPDE.IsWeakPHarmonic.eq_const_of_ge_of_eq
