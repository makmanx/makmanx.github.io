import PropagationTranslated

/-! Actual arbitrary-centre annular lower barriers for continuous weak
supersolutions, with their genuine weak fields. No C1 or classical derivative
of the supersolution is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

def radialAnnulusAt (n : ℕ) (a : Space n) (r R : ℝ) : Set (Space n) :=
  {x | r < dist x a ∧ dist x a < R}

theorem isOpen_radialAnnulusAt (n : ℕ) (a : Space n) (r R : ℝ) :
    IsOpen (radialAnnulusAt n a r R) :=
  (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const)

theorem isBounded_radialAnnulusAt (n : ℕ) (a : Space n) (r R : ℝ) :
    Bornology.IsBounded (radialAnnulusAt n a r R) :=
  (isBounded_ball (x := a) (r := R)).subset (fun _ hx => hx.2)

theorem bounds_of_mem_closure_radialAnnulusAt (n : ℕ) (a : Space n) (r R : ℝ)
    {x : Space n} (hx : x ∈ closure (radialAnnulusAt n a r R)) :
    r ≤ dist x a ∧ dist x a ≤ R := by
  have hc : IsClosed {x : Space n | r ≤ dist x a ∧ dist x a ≤ R} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hs : radialAnnulusAt n a r R ⊆ {x : Space n | r ≤ dist x a ∧ dist x a ≤ R} :=
    fun _ hy => ⟨hy.1.le,hy.2.le⟩
  exact (closure_minimal hs hc) hx

theorem distance_of_mem_frontier_radialAnnulusAt (n : ℕ) (a : Space n) (r R : ℝ)
    {x : Space n} (hx : x ∈ frontier (radialAnnulusAt n a r R)) :
    dist x a = r ∨ dist x a = R := by
  have hb := bounds_of_mem_closure_radialAnnulusAt n a r R hx.1
  have hn : x ∉ radialAnnulusAt n a r R := by
    rw [(isOpen_radialAnnulusAt n a r R).frontier_eq] at hx
    exact hx.2
  by_cases hr : dist x a = r
  · exact Or.inl hr
  · right
    by_contra hR
    exact hn ⟨lt_of_le_of_ne hb.1 (Ne.symm hr),lt_of_le_of_ne hb.2 hR⟩

theorem continuousOn_annularRadialBarrier_sub_closure
    (n : ℕ) {p r R : ℝ} (hr : 0 < r) (a : Space n) :
    ContinuousOn (fun x : Space n => annularRadialBarrier n p r R (x-a))
      (closure (radialAnnulusAt n a r R)) := by
  have hf : ContinuousOn (fun x : Space n => fundamentalPotential n 1 p (x-a))
      (closure (radialAnnulusAt n a r R)) := by
    apply (contDiffOn_fundamentalPotential_sub n 1 p a).continuousOn.mono
    intro x hx
    have hd := hr.trans_le (bounds_of_mem_closure_radialAnnulusAt n a r R hx).1
    exact dist_pos.mp hd
  exact (continuousOn_const.sub hf).div_const _

/-- The actual radial barrier lies below every continuous weak supersolution
from the displayed ordinary two-sphere data. No W0-test membership, classical
derivative or barrier comparison is supplied as an assumption. -/
theorem annularRadialBarrier_le_of_continuous_weak_supersolution
    {n : ℕ} (hn : 2 ≤ n) {p r R m : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hrR : r < R) (a : Space n)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p (radialAnnulusAt n a r R) u g)
    (hc : ContinuousOn u (closure (radialAnnulusAt n a r R)))
    (hinner : ∀ x : Space n, dist x a = r → m ≤ u x)
    (houter : ∀ x : Space n, dist x a = R → 0 ≤ u x) :
    ∀ x ∈ radialAnnulusAt n a r R,
      m * annularRadialBarrier n p r R (x-a) ≤ u x := by
  have hsub : radialAnnulusAt n a r R ⊆ {x : Space n | x ≠ a} := by
    intro x hx
    exact dist_pos.mp (hr.trans hx.1)
  have hw := (((isWeakPHarmonic_fundamentalPotential_sub_all_p n zero_lt_one hp a).smul
    (-m / annularBarrierDenominator n p r R)).add_const
      (m * fundamentalRadialValue n 1 p R / annularBarrierDenominator n p r R)).mono
        hsub (isOpen_radialAnnulusAt n a r R)
  have heq : EqOn
      (fun x : Space n => (-m / annularBarrierDenominator n p r R) *
        fundamentalPotential n 1 p (x-a) +
        m * fundamentalRadialValue n 1 p R / annularBarrierDenominator n p r R)
      (fun x : Space n => m * annularRadialBarrier n p r R (x-a))
      (radialAnnulusAt n a r R) := by
    intro x hx
    unfold annularRadialBarrier
    ring
  obtain ⟨G,hB⟩ := hw.congr_on heq
  have hBc : ContinuousOn (fun x : Space n => m * annularRadialBarrier n p r R (x-a))
      (closure (radialAnnulusAt n a r R)) :=
    continuousOn_const.mul (continuousOn_annularRadialBarrier_sub_closure n hr a)
  apply hB.subsolution.leOn_of_continuous_bounded_boundary_order hu hBc hc hn
    (isBounded_radialAnnulusAt n a r R)
  intro x hx
  rcases distance_of_mem_frontier_radialAnnulusAt n a r R hx with hi | ho
  · have hi' : ‖x-a‖ = r := by simpa only [dist_eq_norm] using hi
    rw [annularRadialBarrier_one_inner n hp hr hrR hi',mul_one]
    exact hinner x hi
  · have ho' : ‖x-a‖ = R := by simpa only [dist_eq_norm] using ho
    rw [annularRadialBarrier_zero_outer n p r R ho',mul_zero]
    exact houter x ho

/-- Positive inner data propagate through the entire annulus for an actual
continuous weak supersolution. -/
theorem annular_positive_of_continuous_weak_supersolution
    {n : ℕ} (hn : 2 ≤ n) {p r R m : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m) (a : Space n)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p (radialAnnulusAt n a r R) u g)
    (hc : ContinuousOn u (closure (radialAnnulusAt n a r R)))
    (hinner : ∀ x : Space n, dist x a = r → m ≤ u x)
    (houter : ∀ x : Space n, dist x a = R → 0 ≤ u x) :
    ∀ x ∈ radialAnnulusAt n a r R, 0 < u x := by
  have hle := annularRadialBarrier_le_of_continuous_weak_supersolution
    hn hp hr hrR a hu hc hinner houter
  intro x hx
  have hpB : 0 < annularRadialBarrier n p r R (x-a) := by
    apply annularRadialBarrier_pos n hp hr hrR
    · simpa only [dist_eq_norm] using hr.trans hx.1
    · simpa only [dist_eq_norm] using hx.2
  exact (mul_pos hm hpB).trans_le (hle x hx)

end BMCompactPDE
#print axioms BMCompactPDE.isOpen_radialAnnulusAt
#print axioms BMCompactPDE.isBounded_radialAnnulusAt
#print axioms BMCompactPDE.bounds_of_mem_closure_radialAnnulusAt
#print axioms BMCompactPDE.distance_of_mem_frontier_radialAnnulusAt
#print axioms BMCompactPDE.continuousOn_annularRadialBarrier_sub_closure
#print axioms BMCompactPDE.annularRadialBarrier_le_of_continuous_weak_supersolution
#print axioms BMCompactPDE.annular_positive_of_continuous_weak_supersolution
