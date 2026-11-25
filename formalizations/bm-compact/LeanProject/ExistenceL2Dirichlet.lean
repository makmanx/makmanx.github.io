import ExistenceL2Graph

/-! Actual bounded-domain Dirichlet solvability in the p=2, n>=3 subcase.
The closed gradient range is proved from the actual W0 graph and Poincare;
Hilbert projection constructs a genuine W0 correction of arbitrary Sobolev
boundary data. No potential, projection-range closure or minimizer is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

/-- Orthogonal projection onto the actual closed W0 gradient range gives
an actual zero-boundary pair cancelling the first variation of any L2 field. -/
theorem exists_w0L2_gradient_correction {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) (F : VectorL2 n Ω) :
    ∃ w : w0L2Graph n Ω, ∀ H ∈ w0L2GradientRange n Ω,
      inner ℝ (F+w0L2Gradient n Ω w) H=0 := by
  let K := w0L2GradientRange n Ω
  have hK : IsClosed (K : Set (VectorL2 n Ω)) := isClosed_w0L2GradientRange hn hΩb
  letI : CompleteSpace K := hK.completeSpace_coe
  have hmem : K.starProjection (-F) ∈ K := K.starProjection_apply_mem (-F)
  obtain ⟨w,hw⟩ : ∃ w : w0L2Graph n Ω,
      w0L2Gradient n Ω w=K.starProjection (-F) := hmem
  refine ⟨w,?_⟩
  intro H hH
  have he := Submodule.starProjection_inner_eq_zero (K := K) (-F) H hH
  rw [←hw] at he
  have ha : -F-w0L2Gradient n Ω w=-(F+w0L2Gradient n Ω w) := by abel
  rw [ha,inner_neg_left] at he
  exact neg_eq_zero.mp he

/-- For any actual W1,2 boundary datum on a bounded open domain in n>=3,
construct a genuine W0,2 correction whose sum with the datum is weak harmonic.
No continuity, classical regularity or Dirichlet existence theorem is a premise. -/
theorem exists_weak_harmonic_L2_Dirichlet {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : Space n → ℝ} {gf : Space n → Space n} (hf : SobolevPair 2 Ω f gf) :
    ∃ w : Space n → ℝ, ∃ gw : Space n → Space n,
      ZeroBoundarySobolevPair 2 Ω w gw ∧
      WeakPHarmonicPair 2 Ω (f+w) (gf+gw) := by
  let μ := volume.restrict Ω
  have hgf : MemLp gf 2 μ := by simpa [μ] using hf.2.2.1
  let F : VectorL2 n Ω := hgf.toLp gf
  obtain ⟨w,hw⟩ := exists_w0L2_gradient_correction hn hΩb F
  have hw0 : ZeroBoundarySobolevPair 2 Ω
      (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) := w.2
  refine ⟨(w.1.1 : Space n → ℝ),(w.1.2 : Space n → Space n),hw0,?_⟩
  apply weakPHarmonicPair_of_sobolev_smooth_equation hΩ (hf.add hw0.1)
  intro φ hφ
  have hφ0 := hφ.zeroBoundarySobolevPair (by norm_num : (1 : ℝ)<2)
  have hφm : MemLp φ 2 μ := by simpa [μ] using hφ0.1.2.1
  have hgφm : MemLp (gradient φ) 2 μ := by simpa [μ] using hφ0.1.2.2.1
  let Φ : ScalarL2 n Ω := hφm.toLp φ
  let H : VectorL2 n Ω := hgφm.toLp (gradient φ)
  have hθ : (Φ,H) ∈ w0L2Graph n Ω := by
    exact hφ0.congr (MemLp.coeFn_toLp hφm).symm (MemLp.coeFn_toLp hgφm).symm
  have hHr : H ∈ w0L2GradientRange n Ω := by
    exact ⟨⟨(Φ,H),hθ⟩,rfl⟩
  have he := hw H hHr
  change inner ℝ (F+w.1.2) H=0 at he
  rw [L2.inner_def] at he
  have hFlux (v : Space n) : pFlux (2 : ℝ) v=v := by simp [pFlux]
  have hAe : (fun x : Space n => inner ℝ ((F+w.1.2) x) (H x)) =ᵐ[μ]
      (fun x => fluxPairing (2 : ℝ) (gf+(w.1.2 : Space n → Space n)) (gradient φ) x) := by
    filter_upwards [Lp.coeFn_add F w.1.2,MemLp.coeFn_toLp hgf,
      MemLp.coeFn_toLp hgφm] with x hsum hF hH
    simp only [fluxPairing,hFlux,Pi.add_apply]
    rw [hsum]
    change inner ℝ ((hgf.toLp gf) x+(w.1.2 : Space n → Space n) x)
      ((hgφm.toLp (gradient φ)) x) =
        inner ℝ (gf x+(w.1.2 : Space n → Space n) x) (gradient φ x)
    rw [hF,hH]
  exact (integral_congr_ae hAe).symm.trans he

end BMCompactPDE
#print axioms BMCompactPDE.exists_w0L2_gradient_correction
#print axioms BMCompactPDE.exists_weak_harmonic_L2_Dirichlet
