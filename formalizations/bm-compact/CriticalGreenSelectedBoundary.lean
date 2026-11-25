import NextRootContinuousOrder
import BallGreenCore

/-! For decreasing annular approximants the first annulus already controls the
selected representative near the obstacle. Pointwise convergence of the
selected representative is unnecessary. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace BMCompactPDE

theorem continuous_selected_annular_limit_at_obstacle
    {n : ℕ} {K : Set (Space n)} (hK : IsClosed K)
    {O : Set (Space n)} (hO : IsOpen O) (hKO : K ⊆ O)
    {G : ℕ → Space n → ℝ} {v w : Space n → ℝ}
    (hG : Continuous (G 0)) (hGK : ∀ x ∈ K, G 0 x = 0)
    (hbound : ∀ j x, x ∈ O → G j x ≤ G 0 x)
    (hpoint : ∀ x, Tendsto (fun j => G j x) atTop (𝓝 (v x)))
    (hvw : v =ᵐ[volume.restrict Kᶜ] w) (hwc : ContinuousOn w Kᶜ)
    (hwK : ∀ x ∈ K, w x = 0) (hw0 : ∀ x, 0 ≤ w x) : Continuous w := by
  have hD : IsOpen (O \ K) := hO.sdiff hK
  have hsub : O \ K ⊆ Kᶜ := fun _ hx => hx.2
  have hAE := ae_restrict_of_ae_restrict_of_subset hsub hvw
  have hcmp := leOn_of_ae_le_continuousOn_actual hD (hwc.mono hsub) hG.continuousOn (by
    filter_upwards [hAE, ae_restrict_mem hD.measurableSet] with x hx hD
    rw [←hx]
    exact le_of_tendsto (hpoint x) (Eventually.of_forall (fun j => hbound j x hD.1)))
  rw [continuous_iff_continuousAt]
  intro a
  by_cases ha : a ∈ K
  · have hupper : ∀ᶠ x in 𝓝 a, w x ≤ G 0 x := by
      filter_upwards [hO.mem_nhds (hKO ha)] with x hx
      by_cases hxK : x ∈ K
      · rw [hwK x hxK, hGK x hxK]
      · exact hcmp x ⟨hx,hxK⟩
    have hlim : Tendsto (G 0) (𝓝 a) (𝓝 0) := hGK a ha ▸ hG.tendsto a
    change Tendsto w (𝓝 a) (𝓝 (w a))
    rw [hwK a ha]
    exact tendsto_const_nhds.squeeze' hlim (Eventually.of_forall hw0) hupper
  · exact hwc.continuousAt (hK.isOpen_compl.mem_nhds ha)

end BMCompactPDE

#print axioms BMCompactPDE.continuous_selected_annular_limit_at_obstacle
