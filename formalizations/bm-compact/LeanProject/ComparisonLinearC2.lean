import ComparisonLinearC1
import RootClassicalGradientIdentification
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Genuine interior C2 regularity for the actual constant-source linear weak
PDE, n>=3. The weak-gradient component equations are derived from the supplied
weak equation. Their constructed continuity and the actual linear C1 theorem
give a C1 weak-gradient field; actual weak-gradient uniqueness identifies it
with the classical derivative. No Hessian or regularity premise is supplied
to the representative-construction endpoint. This is an interior p=2 result. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- An already continuous actual linear weak solution has two continuous
classical derivatives in its arbitrary open domain. The needed derivative
equations and continuous gradient fields are constructed from the weak PDE. -/
theorem WeakPSourcePair.contDiffOn_two_of_continuous_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (huc : ContinuousOn u Ω) (hn : 3≤n) :
    ContDiffOn ℝ 2 u Ω := by
  have hC1 := hu.contDiffOn_one_of_continuous_two huc hn
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
  obtain ⟨G,H,hGc,_,hSobD,hH⟩ :=
    huU.exists_continuous_weak_gradient_two hSobU hn hU.2.1 hD
  have hG1 : ContDiffOn ℝ 1 G D := by
    apply (contDiffOn_piLp 2).2
    intro i
    exact (hH i).source_zero.contDiffOn_one_of_continuous_two
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp_continuousOn hGc) hn
  have hEq := hSobD.2.2.2.eqOn_classical_gradient_of_continuous
    hD.1 (hC1.mono hDΩ) hGc
  have hFD : ContDiffOn ℝ 1 (fderiv ℝ u) D := by
    have hdual : ContDiff ℝ 1 (toDual ℝ (Space n)) :=
      (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    refine (hdual.comp_contDiffOn hG1).congr ?_
    intro y hy
    change fderiv ℝ u y = (toDual ℝ (Space n)) (G y)
    rw [hEq hy,toDual_gradient]
  have hC2D : ContDiffOn ℝ 2 u D := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hD.1).2
    refine ⟨(hC1.mono hDΩ).differentiableOn (by norm_num),?_,hFD⟩
    intro he
    simp at he
  have hxD : x∈D := mem_ball_self (by linarith only [hρ] : 0<ρ/4)
  exact (hC2D.contDiffAt (hD.1.mem_nhds hxD)).contDiffWithinAt

/-- The actual raw constant-source linear weak equation constructs a C2
representative, equal a.e. to the supplied scalar and satisfying the same weak
PDE with the SAME supplied gradient field. No C0, C1, C2, Hessian, global norm,
bounded-domain or classical derivative premise is present. -/
theorem WeakPSourcePair.exists_C2_weak_representative_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hn : 3≤n) :
    ∃ v : Space n → ℝ,ContDiffOn ℝ 2 v Ω ∧
      u =ᵐ[volume.restrict Ω] v ∧ WeakPSourcePair 2 c Ω v g := by
  obtain ⟨v,hvC1,hae,hv⟩ := hu.exists_C1_weak_representative_two hn
  exact ⟨v,hv.contDiffOn_two_of_continuous_two hvC1.continuousOn hn,hae,hv⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.contDiffOn_two_of_continuous_two
#print axioms BMCompactPDE.WeakPSourcePair.exists_C2_weak_representative_two
