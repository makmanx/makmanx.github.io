import PotentialTruncatedEnergy

/-! Two-sided actual DeGiorgi energy estimates. Oddness of the nonlinear flux
turns actual weak supersolutions into subsolutions; ordinary lower truncations
then inherit the genuine upper-level estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSupersolutionPair.neg_subsolution
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) :
    WeakPSubsolutionPair p Ω (fun x => -u x) (fun x => -g x) := by
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    have hs := (hu.2.2.1 D hD).smul (-1)
    exact hs.congr (Eventually.of_forall (fun x => by simp))
      (Eventually.of_forall (fun x => by simp))
  · intro D hD θ h hθ hθ0
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ hθ0
    have hf : fluxPairing p (fun x => -g x) h = -fluxPairing p g h := by
      funext x
      simp only [fluxPairing,pFlux_neg,inner_neg_left,Pi.neg_apply]
    rw [hf]
    refine ⟨hi.neg,?_⟩
    simp only [Pi.neg_apply]
    rw [integral_neg]
    linarith

theorem WeakPSupersolutionPair.caccioppoli_lower_natPow
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, if u x<k then η x^M*‖g x‖^p else 0) ≤
      (M : ℝ)^p * ∫ x in D, (max (k-u x) 0)^p * ‖gradient η x‖^p := by
  have he := hu.neg_subsolution.caccioppoli_upper_natPow hD hη hη0 hη1 hm (-k)
  simpa only [neg_lt_neg_iff,norm_neg,sub_neg_eq_add,neg_add_eq_sub] using he

theorem WeakPHarmonicPair.caccioppoli_lower_natPow
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, if u x<k then η x^M*‖g x‖^p else 0) ≤
      (M : ℝ)^p * ∫ x in D, (max (k-u x) 0)^p * ‖gradient η x‖^p :=
  hu.supersolution.caccioppoli_lower_natPow hD hη hη0 hη1 hm k

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSupersolutionPair.neg_subsolution
#print axioms BMCompactPDE.WeakPSupersolutionPair.caccioppoli_lower_natPow
#print axioms BMCompactPDE.WeakPHarmonicPair.caccioppoli_lower_natPow
