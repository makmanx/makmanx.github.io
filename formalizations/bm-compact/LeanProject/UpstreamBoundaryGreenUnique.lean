import UpstreamBoundaryExteriorComparison
import SupConvolutionGreenTail
import WeakHarmonicScaling

/-! Actual uniqueness for the existing critical/supercritical exterior Green
predicate, on arbitrary compact sets when such functions exist. Bounded actual
remainders and the proved diverging radial profile derive scaled infinity
order; continuous boundary data and the true weak PDE give comparison. No
finite remainder limit, gradient regularity or uniqueness is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_bounded_green_scaled_infinity_order
    {n : ℕ} {σ p : ℝ} (hn : 1<(n:ℝ)) (hpn : (n:ℝ)≤p) (hσ : 0<σ)
    {G H : Space n → ℝ} (hG : HasBoundedGreenRemainder n σ p G)
    (hH : HasBoundedGreenRemainder n σ p H) {δ : ℝ} (hδ : 0<δ) :
    ∀ η : ℝ,0<η → ∀ᶠ x in cocompact (Space n),G x-((1+δ) • H) x<η := by
  obtain ⟨C,hC,hGC⟩ := hG
  obtain ⟨A,hA,hHA⟩ := hH
  have hF := tendsto_fundamentalPotential_atTop n hn hpn hσ
  intro η _
  have hlarge : ∀ᶠ x in cobounded (Space n),
      (C+(1+δ)*A-η)/δ<fundamentalPotential n σ p x :=
    hF.eventually (eventually_gt_atTop _)
  have hall : ∀ᶠ x in cobounded (Space n),G x-((1+δ) • H) x<η := by
    filter_upwards [hGC,hHA,hlarge] with x hxG hxH hxF
    have hg : G x≤fundamentalPotential n σ p x+C := by linarith only [(abs_le.mp hxG).2]
    have hh : fundamentalPotential n σ p x-A≤H x := by linarith only [(abs_le.mp hxH).1]
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith only [hδ] : 0≤1+δ)
    have hf : C+(1+δ)*A-η<fundamentalPotential n σ p x*δ := (div_lt_iff₀ hδ).mp hxF
    simp only [Pi.smul_apply,smul_eq_mul]
    nlinarith only [hg,hmul,hf]
  simpa only [Metric.cobounded_eq_cocompact] using hall

theorem IsExteriorGreen.unique {n : ℕ} {σ p : ℝ} {K : Set (Space n)}
    {G H : Space n → ℝ} (hG : IsExteriorGreen n σ p K G)
    (hH : IsExteriorGreen n σ p K H) : G=H := by
  obtain ⟨hn,hpn,hσ,hK,hKne,hGc,hGK,⟨g,hGPDE⟩,hGR⟩ := hG
  obtain ⟨_,_,_,_,_,hHc,hHK,⟨h,hHPDE⟩,hHR⟩ := hH
  have hn1 : 1<n := by exact_mod_cast hn
  have hn2 : 2≤n := Nat.succ_le_iff.mpr hn1
  have hscaled (δ : ℝ) (hδ : 0<δ) : ∀ x∈Kᶜ,G x≤((1+δ) • H) x := by
    apply hGPDE.leOn_compl_of_continuous_boundary_order_and_infinity_order hK hn2 (hHPDE.smul (1+δ))
      hGc (continuous_const.smul hHc)
    · intro x hx
      simp only [hGK hx,hHK hx,Pi.smul_apply,smul_zero]
      exact le_rfl
    · exact upstream_bounded_green_scaled_infinity_order hn hpn hσ hGR hHR hδ
  have hscaled' (δ : ℝ) (hδ : 0<δ) : ∀ x∈Kᶜ,H x≤((1+δ) • G) x := by
    apply hHPDE.leOn_compl_of_continuous_boundary_order_and_infinity_order hK hn2 (hGPDE.smul (1+δ))
      hHc (continuous_const.smul hGc)
    · intro x hx
      simp only [hGK hx,hHK hx,Pi.smul_apply,smul_zero]
      exact le_rfl
    · exact upstream_bounded_green_scaled_infinity_order hn hpn hσ hHR hGR hδ
  have hparam : Tendsto (fun j : ℕ=>((j:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  funext x
  by_cases hx : x∈K
  · exact (hGK hx).trans (hHK hx).symm
  · apply le_antisymm
    · have ht : Tendsto (fun j : ℕ=>((1+((j:ℝ)+1)⁻¹) • H) x) atTop (𝓝 (H x)) := by
        simpa only [Pi.smul_apply,smul_eq_mul,add_zero,one_mul] using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).add hparam).mul_const (H x)
      exact ge_of_tendsto ht (Eventually.of_forall (fun j=>hscaled _ (inv_pos.mpr (by positivity)) x hx))
    · have ht : Tendsto (fun j : ℕ=>((1+((j:ℝ)+1)⁻¹) • G) x) atTop (𝓝 (G x)) := by
        simpa only [Pi.smul_apply,smul_eq_mul,add_zero,one_mul] using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1)).add hparam).mul_const (G x)
      exact ge_of_tendsto ht (Eventually.of_forall (fun j=>hscaled' _ (inv_pos.mpr (by positivity)) x hx))

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.unique
