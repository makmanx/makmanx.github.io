import UpstreamGreenAnnularFamily
import UpstreamGreenLocalGradientBound
import UpstreamGreenUniformLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-! Actual scalar limits of the constructed supercritical annular family.
Eventual radial antitonicity constructs pointwise limits. Actual compact
scalar bounds and the weak-PDE Caccioppoli estimate supply all norm ceilings
used for Morrey and local uniform convergence. No candidate family, limit,
gradient ceiling, Holder bound or scalar convergence is an input. The weak
PDE of the limit and continuity across K remain separate constructions. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_radial_eventual_antitone_pointwise_limit
    {n : ℕ} {R : ℕ → ℝ} (hRmono : Monotone R) (hRlim : Tendsto R atTop atTop)
    {G : ℕ → Space n → ℝ} (hG0 : ∀ j x,0≤G j x)
    (horder : ∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) :
    ∃ v : Space n → ℝ,∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x)) := by
  classical
  have hex (x : Space n) : ∃ l : ℝ,Tendsto (fun j=>G j x) atTop (𝓝 l) := by
    obtain ⟨J,hJ⟩ := (hRlim.eventually (eventually_gt_atTop ‖x‖)).exists
    have hxJ : x∈ball (0 : Space n) (R J) := by simpa only [mem_ball,dist_zero_right] using hJ
    have hanti : Antitone (fun j : ℕ=>G (j+J) x) := by
      intro j k hjk
      apply horder (j+J) (k+J) (Nat.add_le_add_right hjk J) x
      exact ball_subset_ball (hRmono (by omega : J≤j+J)) hxJ
    have hbelow : BddBelow (range (fun j : ℕ=>G (j+J) x)) := by
      refine ⟨0,?_⟩
      rintro _ ⟨j,rfl⟩
      exact hG0 (j+J) x
    exact ⟨_,(tendsto_add_atTop_iff_nat J).mp (tendsto_atTop_ciInf hanti hbelow)⟩
  choose v hv using hex
  exact ⟨v,hv⟩

private theorem green_local_domain_collar {n : ℕ} {D Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hD : LocalDomain D Ω) :
    ∃ U : Set (Space n),LocalDomain U Ω ∧ LocalDomain D U := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨r,hr,hthick⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
  let U : Set (Space n) := thickening r (closure D)
  refine ⟨U,⟨isOpen_thickening,hK.isBounded.thickening,?_⟩,
    hD.1,hD.2.1,self_subset_thickening hr (closure D)⟩
  exact (closure_thickening_subset_cthickening r (closure D)).trans hthick

set_option maxHeartbeats 1800000 in
theorem exists_canonical_annular_green_scalar_limit_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n : ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (h0 : (0 : Space n)∈K) :
    ∃ R : ℕ → ℝ,∃ G : ℕ → Space n → ℝ,∃ Γ : ℕ → Space n → Space n,
      ∃ v : Space n → ℝ,
      (∀ j,0<R j ∧ K⊆ball 0 (R j)) ∧ StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ j,Continuous (G j)) ∧ (∀ j x,x∈K → G j x=0) ∧
      (∀ j x,x∉ball 0 (R j) → G j x=fundamentalRadialValue n (canonicalSphereArea n) p (R j)) ∧
      (∀ j,MemLp (Γ j) (ENNReal.ofReal p) volume) ∧
      (∀ j B,Bornology.IsBounded B → SobolevPair p B (G j) (Γ j)) ∧
      (∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (Γ j)) ∧
      (∀ j x,0≤G j x ∧ G j x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      (∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) ∧
      ContinuousOn v Kᶜ ∧ (∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x))) ∧
      (∀ x∈K,v x=0) ∧ (∀ x,0≤v x ∧ v x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      ∀ D : Set (Space n),LocalDomain D Kᶜ → TendstoUniformlyOn G v atTop (closure D) := by
  classical
  obtain ⟨R,G,Γ,hR,hRmono,hRlim,hGc,hGK,hGout,hΓ,hSob,hH,hB,horder,_⟩ :=
    exists_canonical_annular_green_family_supercritical hn hnp hK h0
  obtain ⟨v,hpoint⟩ := green_radial_eventual_antitone_pointwise_limit hRmono.monotone hRlim
    (fun j x=>(hB j x).1) horder
  have hvK (x : Space n) (hx : x∈K) : v x=0 := by
    apply tendsto_nhds_unique (hpoint x)
    simpa only [hGK _ x hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0))
  have hvB (x : Space n) : 0≤v x ∧ v x≤fundamentalPotential n (canonicalSphereArea n) p x :=
    ⟨ge_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>(hB j x).1)),
      le_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>(hB j x).2))⟩
  have hnR : 1<(n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hp : 1<p := hnR.trans hnp
  have hn1 : 1≤n := (by decide : 1≤2).trans hn
  have hΩ : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hFcont : Continuous (fundamentalPotential n (canonicalSphereArea n) p : Space n → ℝ) :=
    continuous_fundamentalPotential_supercritical n (canonicalSphereArea n) hnR hnp
  have hlocal (D : Set (Space n)) (hD : LocalDomain D Kᶜ) :
      ContinuousOn v D ∧ TendstoUniformlyOn G v atTop (closure D) := by
    obtain ⟨U,hU,hDU⟩ := green_local_domain_collar hΩ hD
    obtain ⟨W,hW,hUW⟩ := green_local_domain_collar hΩ hU
    have hWU : W⊆Kᶜ := subset_closure.trans hW.2.2
    have hUWsub : U⊆W := subset_closure.trans hUW.2.2
    have hDUsub : D⊆U := subset_closure.trans hDU.2.2
    have himage : IsCompact ((fundamentalPotential n (canonicalSphereArea n) p) '' closure W) :=
      hW.2.1.isCompact_closure.image hFcont
    obtain ⟨B,hBpos,hBF⟩ := himage.isBounded.exists_pos_norm_le
    have habs (j : ℕ) (x : Space n) (hx : x∈W) : |G j x|≤B := by
      have hFx : ‖fundamentalPotential n (canonicalSphereArea n) p x‖≤B :=
        hBF _ (mem_image_of_mem _ (subset_closure hx))
      rw [abs_of_nonneg (hB j x).1]
      exact (hB j x).2.trans ((le_abs_self _).trans hFx)
    obtain ⟨T,hT,hWT⟩ := hW.2.1.subset_ball_lt 0 (0 : Space n)
    obtain ⟨J,hJ⟩ := (hRlim.eventually (eventually_ge_atTop T)).exists
    have hWR (j : ℕ) : W⊆ball 0 (R (j+J)) :=
      hWT.trans (ball_subset_ball (hJ.trans (hRmono.monotone (by omega : J≤j+J))))
    have hHtail (j : ℕ) : WeakPHarmonicPair p W (G (j+J)) (Γ (j+J)) := by
      apply (hH (j+J)).mono _ hW.1
      intro x hx
      exact ⟨hWR j hx,hWU hx⟩
    obtain ⟨C,hC,hCG⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp hW.1 hUW
    have hgrad (j : ℕ) :
        (eLpNorm (Γ (j+J)) (ENNReal.ofReal p) (volume.restrict U)).toReal≤C*B :=
      hCG _ _ (hHtail j) B hBpos.le (fun x hx=>habs (j+J) x hx)
    letI : IsFiniteMeasure (volume.restrict U) :=
      isFiniteMeasure_restrict.mpr hU.2.1.measure_lt_top.ne
    let M₀ : ℝ := (eLpNorm (fun _ : Space n=>B) (ENNReal.ofReal p) (volume.restrict U)).toReal
    have hconst : MemLp (fun _ : Space n=>B) (ENNReal.ofReal p) (volume.restrict U) := memLp_const B
    have hscalar (j : ℕ) :
        (eLpNorm (G (j+J)) (ENNReal.ofReal p) (volume.restrict U)).toReal≤M₀ := by
      apply ENNReal.toReal_mono hconst.eLpNorm_ne_top
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
      simpa only [Real.norm_eq_abs,abs_of_pos hBpos] using habs (j+J) x (hUWsub hx)
    obtain ⟨hvcU,huni⟩ := continuous_sobolev_family_pointwise_limit_locally_uniform
      hn1 hnp hU.1 (show 0≤M₀ from ENNReal.toReal_nonneg) (mul_nonneg hC hBpos.le)
      (fun j=>hSob (j+J) U hU.2.1) (fun j=>(hGc (j+J)).continuousOn) hscalar hgrad
      (fun x _=>(hpoint x).comp (tendsto_add_atTop_nat J))
    refine ⟨hvcU.mono hDUsub,?_⟩
    intro V hV
    obtain ⟨N,hN⟩ := eventually_atTop.mp (huni D hDU V hV)
    refine eventually_atTop.mpr ⟨N+J,?_⟩
    intro j hj
    have hsub : N≤j-J := by omega
    have hshift : j-J+J=j := Nat.sub_add_cancel (by omega : J≤j)
    simpa only [hshift] using hN (j-J) hsub
  have hvc : ContinuousOn v Kᶜ := by
    intro x hx
    obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    let D : Set (Space n) := ball x (ρ/2)
    have hD : LocalDomain D Kᶜ := by
      refine ⟨isOpen_ball,isBounded_ball,?_⟩
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball)
    have hxD : x∈D := mem_ball_self (half_pos hρ)
    exact ((hlocal D hD).1.continuousAt (hD.1.mem_nhds hxD)).continuousWithinAt
  exact ⟨R,G,Γ,v,hR,hRmono,hRlim,hGc,hGK,hGout,hΓ,hSob,hH,hB,horder,hvc,hpoint,hvK,hvB,
    fun D hD=>(hlocal D hD).2⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_annular_green_scalar_limit_supercritical
