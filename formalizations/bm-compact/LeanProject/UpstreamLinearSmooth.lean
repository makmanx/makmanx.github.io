import UpstreamLinearC2

/-! Genuine C-infinity interior regularity of the actual constant-source linear
weak PDE in all dimensions n>=2. The proof repeatedly derives harmonic weak
gradient components; their actual regularity is constructed at each order.
The smoothness order below is the inner ENat infinity, never analytic omega. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_linear_contDiffOn_nat (k : ℕ) :
    ∀ {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
      {u : Space n → ℝ} {g : Space n → Space n},
      WeakPSourcePair 2 c Ω u g → ContinuousOn u Ω → 2≤n →
      ContDiffOn ℝ k u Ω := by
  induction k with
  | zero =>
    intro n c Ω u g hu huc hn
    exact contDiffOn_zero.mpr huc
  | succ k ih =>
    intro n c Ω u g hu huc hn
    have hC1 := hu.contDiffOn_one_of_continuous_two_all_dimensions huc hn
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
      huU.exists_continuous_weak_gradient_two_all_dimensions hSobU hn hU.2.1 hD
    have hGk : ContDiffOn ℝ k G D := by
      apply (contDiffOn_piLp 2).2
      intro i
      exact ih (hH i).source_zero
        ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp_continuousOn hGc) hn
    have hEq := hSobD.2.2.2.eqOn_classical_gradient_of_continuous
      hD.1 (hC1.mono hDΩ) hGc
    have hFD : ContDiffOn ℝ k (fderiv ℝ u) D := by
      have hdual : ContDiff ℝ k (toDual ℝ (Space n)) :=
        (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff
      refine (hdual.comp_contDiffOn hGk).congr ?_
      intro y hy
      change fderiv ℝ u y=(toDual ℝ (Space n)) (G y)
      rw [hEq hy,toDual_gradient]
    have hCnext : ContDiffOn ℝ ((k : ℕ∞ω)+1) u D := by
      apply (contDiffOn_succ_iff_fderiv_of_isOpen (n:=(k : ℕ∞ω)) hD.1).2
      refine ⟨(hC1.mono hDΩ).differentiableOn (by norm_num),?_,hFD⟩
      intro he
      simp at he
    have hCnextNat : ContDiffOn ℝ (k+1 : ℕ) u D := by
      simpa only [Nat.cast_add,Nat.cast_one] using hCnext
    have hxD : x∈D := mem_ball_self (by linarith only [hρ] : 0<ρ/4)
    exact (hCnextNat.contDiffAt (hD.1.mem_nhds hxD)).contDiffWithinAt

theorem WeakPSourcePair.contDiffOn_infty_of_continuous_two_all_dimensions
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (huc : ContinuousOn u Ω) (hn : 2≤n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u Ω := by
  exact contDiffOn_infty.mpr (fun k => upstream_linear_contDiffOn_nat k hu huc hn)

/-- A raw actual constant-source weak solution at p=2 constructs a genuine
C-infinity representative on any open domain in n>=2, preserving the SAME
supplied weak-gradient field and source equation. No regularity is an input. -/
theorem WeakPSourcePair.exists_smooth_weak_representative_two_all_dimensions
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hn : 2≤n) :
    ∃ v : Space n → ℝ,ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v Ω ∧
      u =ᵐ[volume.restrict Ω] v ∧ WeakPSourcePair 2 c Ω v g := by
  obtain ⟨v,hvc,hae,hv⟩ := hu.exists_continuous_weak_representative_allp hn
  exact ⟨v,hv.contDiffOn_infty_of_continuous_two_all_dimensions hvc hn,hae,hv⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.contDiffOn_infty_of_continuous_two_all_dimensions
#print axioms BMCompactPDE.WeakPSourcePair.exists_smooth_weak_representative_two_all_dimensions
