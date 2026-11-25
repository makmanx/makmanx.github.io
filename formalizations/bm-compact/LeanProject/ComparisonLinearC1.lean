import ComparisonLinearContinuity
import RootLocalContinuousGradient

/-! Genuine interior C1 regularity for the actual constant-source linear weak
PDE, n>=3. Scalar continuity is selected from the weak PDE, and the continuous
weak gradient is constructed from the derived component equations. Neither
C1 nor gradient continuity nor a Hessian is an input to the final endpoint.
No boundary regularity or nonlinear p!=2 conclusion is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- An already continuous actual linear weak solution is C1 in its arbitrary
open domain. All required Sobolev data and continuous weak-gradient fields are
constructed locally; no global norm or bounded-domain assumption is present. -/
theorem WeakPSourcePair.contDiffOn_one_of_continuous_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (huc : ContinuousOn u Ω) (hn : 3≤n) :
    ContDiffOn ℝ 1 u Ω := by
  intro x hx
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hu.2.1 x hx
  let U : Set (Space n) := ball x (ρ/2)
  let D : Set (Space n) := ball x (ρ/4)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    exact closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball)
  have hD : LocalDomain D U := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    exact closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (by linarith only [hρ] : ρ/4<ρ/2))
  have hUΩ : U⊆Ω := subset_closure.trans hU.2.2
  have hDΩ : D⊆Ω := (subset_closure.trans hD.2.2).trans hUΩ
  have huU := hu.mono_actual hUΩ hU.1
  have hSobU := hu.2.2.1 U hU
  obtain ⟨G,H,hGc,_,hSobD,_⟩ :=
    huU.exists_continuous_weak_gradient_two hSobU hn hU.2.1 hD
  have hC1D := hSobD.contDiffOn_one_of_continuous_gradient hD.1 (huc.mono hDΩ) hGc
  have hxD : x∈D := mem_ball_self (by linarith only [hρ] : 0<ρ/4)
  exact (hC1D.contDiffAt (hD.1.mem_nhds hxD)).contDiffWithinAt

/-- The actual raw linear weak source equation constructs a genuine C1
representative, equal a.e. to the supplied scalar and satisfying the same weak
PDE with the SAME supplied gradient field. No regularity premise is supplied. -/
theorem WeakPSourcePair.exists_C1_weak_representative_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hn : 3≤n) :
    ∃ v : Space n → ℝ,ContDiffOn ℝ 1 v Ω ∧
      u =ᵐ[volume.restrict Ω] v ∧ WeakPSourcePair 2 c Ω v g := by
  have h2n : (2 : ℝ)<(n : ℝ) := by
    have hh : 2<n := lt_of_lt_of_le (by decide : 2<3) hn
    exact_mod_cast hh
  obtain ⟨v,hvc,hae,hv⟩ := hu.exists_continuous_weak_representative h2n
  exact ⟨v,hv.contDiffOn_one_of_continuous_two hvc hn,hae,hv⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.contDiffOn_one_of_continuous_two
#print axioms BMCompactPDE.WeakPSourcePair.exists_C1_weak_representative_two
