import RootContinuousWeakGradient
import RootSobolevLocalization

/-! Genuine local C1 bridge from continuous actual Sobolev fields.
Continuity of the weak gradient remains an explicit hypothesis here. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem SobolevPair.contDiffOn_one_of_continuous_gradient
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω)
    (huc : ContinuousOn u Ω) (hgc : ContinuousOn g Ω) :
    ContDiffOn ℝ 1 u Ω := by
  intro x hx
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hhalf : 0<ρ/2 := half_pos hρ
  have hKΩ : closedBall x (ρ/2)⊆Ω :=
    (closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact
    (isCompact_closedBall x (ρ/2)) hΩ hKΩ
  let χ : Space n → ℝ := fun y => Real.smoothTransition (f y)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ)))
  have hs : tsupport χ⊆Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))) f).trans hf.2.2.1
  have hχone (y : Space n) (hy : y∈closedBall x (ρ/2)) : χ y=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 y hy)
  let U : Space n → ℝ := fun y => χ y*u y
  let G : Space n → Space n := fun y => χ y • g y+u y • gradient χ y
  have hUg : SobolevPair p univ U G := hu.mul_smooth_compactSupport_global hΩ hχ hc hs
  have hUc : Continuous U := by
    apply continuous_of_tsupport
    intro y hy
    have hyΩ : y∈Ω := hs (tsupport_mul_subset_left hy)
    exact hχ.continuous.continuousAt.mul (huc.continuousAt (hΩ.mem_nhds hyΩ))
  have hgradχ : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.of_le (by simp))
  have hGc : Continuous G := by
    apply Continuous.add
    · apply continuous_of_tsupport
      intro y hy
      have hyΩ : y∈Ω := hs (tsupport_smul_subset_left χ g hy)
      exact hχ.continuous.continuousAt.smul (hgc.continuousAt (hΩ.mem_nhds hyΩ))
    · apply continuous_of_tsupport
      intro y hy
      have hyΩ : y∈Ω := hs ((tsupport_gradient_subset_actual χ)
        (tsupport_smul_subset_right u (gradient χ) hy))
      exact (huc.continuousAt (hΩ.mem_nhds hyΩ)).smul hgradχ.continuousAt
  have hGs : tsupport G⊆tsupport χ :=
    (tsupport_add _ _).trans (union_subset (tsupport_smul_subset_left χ g)
      ((tsupport_smul_subset_right u (gradient χ)).trans (tsupport_gradient_subset_actual χ)))
  have hGcompact : HasCompactSupport G :=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport G) hGs
  have hC1 := hUg.contDiff_one_of_continuous_gradient_univ hUc hGc hGcompact
  have he : u=ᶠ[𝓝 x] U := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hhalf)] with y hy
    change u y=χ y*u y
    rw [hχone y (ball_subset_closedBall hy),one_mul]
  exact (hC1.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.contDiffOn_one_of_continuous_gradient
