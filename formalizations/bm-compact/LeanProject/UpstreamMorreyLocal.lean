import UpstreamMorreyRepresentative
import RootSobolevLocalization
import RootSourceContinuity

/-! Actual local representative selection above the dimension. Global compact
models and their continuous Morrey representatives are constructed from the
distributional Sobolev graph. Raw scalar continuity is never an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem SobolevPair.vanishingEssentialOscillation_supercritical
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hn : 1≤n) (hnp : (n:ℝ)<p) :
    BMCompactRepresentative.VanishingEssentialOscillation volume u Ω := by
  obtain ⟨A,hA⟩ := exists_actual_global_morrey_constant hn hnp
  intro x hx ε hε
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hhalf : 0<ρ/2 := half_pos hρ
  have hKΩ : closedBall x (ρ/2)⊆Ω :=
    (closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact
    (isCompact_closedBall x (ρ/2)) hΩ hKΩ
  let χ : Space n → ℝ := fun y => Real.smoothTransition (a y)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp ha.1
  have hc : HasCompactSupport χ := ha.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ)))
  have hs : tsupport χ⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))) a).trans ha.2.2.1
  have hχone (y : Space n) (hy : y∈closedBall x (ρ/2)) : χ y=1 :=
    Real.smoothTransition.one_of_one_le (ha.2.2.2 y hy)
  let F : Space n → ℝ := fun y => χ y*u y
  let G : Space n → Space n := fun y => χ y • g y+u y • gradient χ y
  have hFG : SobolevPair p univ F G := hu.mul_smooth_compactSupport_global hΩ hχ hc hs
  obtain ⟨v,hvc,hFv,-⟩ := hA F G hFG
  let U : Set (Space n) := ball x (ρ/2) ∩ v ⁻¹' ball (v x) ε
  have hU : IsOpen U := isOpen_ball.inter (hvc.isOpen_preimage _ isOpen_ball)
  have hxU : x∈U := ⟨mem_ball_self hhalf,mem_ball_self hε⟩
  have hUΩ : U⊆Ω := fun y hy => hKΩ (ball_subset_closedBall hy.1)
  refine ⟨U,v x,hU,hxU,hUΩ,?_⟩
  filter_upwards [ae_restrict_of_ae hFv,ae_restrict_mem hU.measurableSet] with y hy hyU
  have huy : u y=v y := by
    simpa only [F,hχone y (ball_subset_closedBall hyU.1),one_mul] using hy
  rw [huy]
  exact (show dist (v y) (v x)<ε from hyU.2).le

/-- Actual local Sobolev data select a unique continuous representative when
p is above the dimension. No PDE or regularity estimate is assumed. -/
theorem exists_unique_continuousRepresentative_of_local_supercritical_sobolev
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hΩ : IsOpen Ω) (hn : 1≤n) (hnp : (n:ℝ)<p)
    (hu : ∀ D,LocalDomain D Ω → SobolevPair p D u g) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      ∀ w : Space n → ℝ,ContinuousOn w Ω → u =ᵐ[volume.restrict Ω] w → EqOn v w Ω := by
  apply BMCompactRepresentative.exists_unique_continuousRepresentative volume hΩ
  intro x hx ε hε
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let D : Set (Space n) := ball x (ρ/2)
  have hD : LocalDomain D Ω := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    exact closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball)
  have hxD : x∈D := mem_ball_self (half_pos hρ)
  obtain ⟨U,a,hU,hxU,hUD,ha⟩ :=
    (hu D hD).vanishingEssentialOscillation_supercritical hD.1 hn hnp x hxD ε hε
  exact ⟨U,a,hU,hxU,hUD.trans (subset_closure.trans hD.2.2),ha⟩

theorem WeakPSourcePair.exists_continuous_weak_representative_supercritical
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hn : 1≤n) (hnp : (n:ℝ)<p) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g := by
  obtain ⟨v,hv,huv,-⟩ :=
    exists_unique_continuousRepresentative_of_local_supercritical_sobolev
      hu.2.1 hn hnp hu.2.2.1
  exact ⟨v,hv,huv,hu.1,hu.2.1,hu.2.2.1.congr_ae huv EventuallyEq.rfl,hu.2.2.2⟩

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.vanishingEssentialOscillation_supercritical
#print axioms BMCompactPDE.exists_unique_continuousRepresentative_of_local_supercritical_sobolev
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_weak_representative_supercritical
