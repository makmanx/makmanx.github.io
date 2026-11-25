import RootDoublingComparison
import ContactManuscriptBridge

/-! Exact bounded manuscript tests reach the critical comparator theorem.
The forced comparison is proved; existence/regularity/convergence of the
forcing approximants remains explicit in the subsequent limit reduction. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSourceSupersolutionPair.manuscript_le_of_noncritical_reg
    {n : ℕ} {p c M : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g : Space n → Space n} (hv : WeakPSourceSupersolutionPair p c Ω v g)
    (hc : 0<c) (hvc : ContinuousOn v Ω) (hvd : DifferentiableOn ℝ v Ω)
    (hv2 : ∀ z∈Ω, gradient v z≠0 → ContDiffAt ℝ 2 v z)
    (hu : BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u)
    (hub : ∀ z∈Ω,u z≤M) (hn : 2≤n) (hD : LocalDomain D Ω)
    (hb : ∀ z∈frontier D,u z≤v z) : ∀ z∈D,u z≤v z := by
  exact hv.viscosity_le_of_noncritical_reg hc hvc hvd hv2
    (hu.local_of_boundedAbove hub) hn hD hb

/-- A limit reduction, not an existence theorem for the actual forcing family.
No comparison conclusion is assumed for any approximant. -/
theorem manuscript_le_of_actual_forced_approximants
    {n : ℕ} {p M : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {c : ℕ → ℝ} {V : ℕ → Space n → ℝ} {G : ℕ → Space n → Space n}
    (hV : ∀ j, WeakPSourceSupersolutionPair p (c j) Ω (V j) (G j))
    (hc : ∀ j, 0<c j) (hVc : ∀ j, ContinuousOn (V j) Ω)
    (hVd : ∀ j, DifferentiableOn ℝ (V j) Ω)
    (hV2 : ∀ j, ∀ z∈Ω, gradient (V j) z≠0 → ContDiffAt ℝ 2 (V j) z)
    (hu : BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u)
    (hub : ∀ z∈Ω,u z≤M) (hn : 2≤n) (hD : LocalDomain D Ω)
    (hb : ∀ j, ∀ z∈frontier D,u z≤V j z)
    (hlim : ∀ z∈D,Tendsto (fun j=>V j z) atTop (𝓝 (v z))) :
    ∀ z∈D,u z≤v z := by
  intro z hz
  have hle (j : ℕ) := (hV j).manuscript_le_of_noncritical_reg (hc j)
    (hVc j) (hVd j) (hV2 j) hu hub hn hD (hb j) z hz
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim z hz) (Eventually.of_forall hle)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.manuscript_le_of_noncritical_reg
#print axioms BMCompactPDE.manuscript_le_of_actual_forced_approximants
