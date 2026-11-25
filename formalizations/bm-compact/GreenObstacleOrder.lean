import UpstreamBoundaryGreenUnique
import GreenAsymptoticBasics

/-! Order of normalized exterior Green functions for nested compact obstacles,
including both the logarithmic and power cases of manuscript Lemma 4.2(c).
The finite constants are ordered whenever both asymptotic limits exist. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology
open scoped Topology
namespace BMCompactPDE

theorem IsExteriorGreen.tendsto_atTop_at_infinity
    {n : ℕ} {σ p : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) : Tendsto u (cobounded (Space n)) atTop := by
  obtain ⟨hn,hp,hσ,_,_,_,_,_,C,_,hC⟩ := hu
  apply Filter.tendsto_atTop.mpr
  intro M
  filter_upwards [hC,(tendsto_fundamentalPotential_atTop n hn hp hσ).eventually
    (eventually_ge_atTop (M+C))] with x hx hM
  linarith only [(abs_le.mp hx).1,hM]

theorem IsExteriorGreen.nonnegative
    {n : ℕ} {σ p : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) (x : Space n) : 0 ≤ u x := by
  have hinf := hu.tendsto_atTop_at_infinity
  obtain ⟨hn,hp,_,hK,_,hc,h0,⟨g,hg⟩,_⟩ := hu
  by_cases hx : x ∈ K
  · rw [h0 hx]
  have hnNat : 1 < n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  have hzero := weakPHarmonicPair_const (hn.trans_le hp) hK.isClosed.isOpen_compl 0
  apply hzero.leOn_compl_of_continuous_boundary_order_and_infinity_order hK hn2 hg
    continuous_const hc (fun y hy => (h0 hy).ge) _ x hx
  intro ε hε
  have he : ∀ᶠ y in cobounded (Space n), 0 - u y < ε := by
    filter_upwards [hinf.eventually (eventually_ge_atTop 0)] with y hy
    linarith only [hy,hε]
  simpa only [Metric.cobounded_eq_cocompact] using he

theorem IsExteriorGreen.antitone_obstacle
    {n : ℕ} {σ p : ℝ} {K L : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) (hv : IsExteriorGreen n σ p L v)
    (hKL : K ⊆ L) : v ≤ u := by
  have hnonneg := hu.nonnegative
  have hinf := hu.tendsto_atTop_at_infinity
  obtain ⟨hn,hp,_,_,_,huC,_,⟨g,hg⟩,A,_,hA⟩ := hu
  obtain ⟨_,_,_,hL,_,hvC,hv0,⟨h,hh⟩,B,_,hB⟩ := hv
  have hnNat : 1 < n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  have hgu := hg.mono (compl_subset_compl.mpr hKL) hL.isClosed.isOpen_compl
  have hscale (δ : ℝ) (hδ : 0 < δ) : v ≤ (1+δ) • u := by
    have horder (y : Space n) (hy : y ∈ L) : v y ≤ ((1+δ) • u) y := by
      rw [hv0 hy]
      exact mul_nonneg (by linarith only [hδ]) (hnonneg y)
    have hinfty (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ y in cocompact (Space n),v y-((1+δ) • u) y < ε := by
      rw [←Metric.cobounded_eq_cocompact]
      filter_upwards [hA,hB,hinf.eventually (eventually_ge_atTop ((A+B)/δ))] with y hyA hyB hlarge
      have hδu := (div_le_iff₀ hδ).mp hlarge
      change v y - (1+δ)*u y < ε
      nlinarith only [(abs_le.mp hyA).1,(abs_le.mp hyB).2,hδu,hε]
    intro y
    by_cases hy : y ∈ L
    · exact horder y hy
    · exact hh.leOn_compl_of_continuous_boundary_order_and_infinity_order hL hn2 (hgu.smul (1+δ))
        hvC (continuous_const.smul huC) horder hinfty y hy
  have ht : Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  intro x
  have hx : Tendsto (fun j : ℕ => ((1+((j:ℝ)+1)⁻¹) • u) x) atTop (𝓝 (u x)) := by
    simpa only [Pi.smul_apply,smul_eq_mul,add_zero,one_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add ht).mul_const (u x)
  exact ge_of_tendsto hx (Eventually.of_forall (fun j => hscale _ (inv_pos.mpr (by positivity)) x))

theorem IsExteriorGreen.asymptotic_constant_antitone_obstacle
    {n : ℕ} {σ p k l : ℝ} {K L : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) (hv : IsExteriorGreen n σ p L v)
    (hKL : K ⊆ L) (hk : HasGreenAsymptotic n σ p u k)
    (hl : HasGreenAsymptotic n σ p v l) : l ≤ k := by
  have hn : 1 < n := by exact_mod_cast hu.1
  have : NeZero n := ⟨by omega⟩
  exact le_of_tendsto_of_tendsto hl hk
    (Eventually.of_forall (fun x => sub_le_sub_right (hu.antitone_obstacle hv hKL x) _))

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.tendsto_atTop_at_infinity
#print axioms BMCompactPDE.IsExteriorGreen.nonnegative
#print axioms BMCompactPDE.IsExteriorGreen.antitone_obstacle
#print axioms BMCompactPDE.IsExteriorGreen.asymptotic_constant_antitone_obstacle
