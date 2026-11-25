import ComparisonSelectedDirichlet
import ContactClassicalForce

/-! Actual constant-source weak equations give noncritical local viscosity
upper and lower test inequalities. The representative can be constructed from
the PDE at 1<p<n. No differentiability of the weak solution is assumed.
These are the noncritical test inequalities, not general critical comparison. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

private theorem comparison_gradient_neg (φ : E → ℝ) (x : E) :
    gradient (-φ) x = -gradient φ x := by
  simp only [gradient,fderiv_neg,map_neg]

private theorem comparison_actualHessian_neg (φ : E → ℝ) (x : E) :
    actualHessian (-φ) x = -actualHessian φ x := by
  have he : fderiv ℝ (-φ) = -(fderiv ℝ φ) := funext (fun y => fderiv_neg)
  simp only [actualHessian,he,fderiv_neg]

private theorem comparison_actualHessianEnd_neg (φ : E → ℝ) (x : E) :
    actualHessianEnd (-φ) x = -actualHessianEnd φ x := by
  simp only [actualHessianEnd,comparison_actualHessian_neg,
    ContinuousLinearMap.toLinearMap_neg,LinearMap.comp_neg]

private theorem comparison_normalizedPLaplacian_neg (p : ℝ) (φ : E → ℝ) (x : E) :
    normalizedPLaplacian p (-φ) x = -normalizedPLaplacian p φ x := by
  have hl : actualLaplacian (-φ) x = -actualLaplacian φ x := by
    simp only [actualLaplacian,comparison_actualHessianEnd_neg,map_neg]
  simp only [normalizedPLaplacian,hl,comparison_gradient_neg,norm_neg,
    comparison_actualHessian_neg,ContinuousLinearMap.neg_apply,map_neg,neg_neg]
  ring

/-- Oddness of the actual Hessian-form classical p-Laplace operator. -/
theorem classicalPLaplacian_neg (p : ℝ) (φ : E → ℝ) (x : E) :
    classicalPLaplacian p (-φ) x = -classicalPLaplacian p φ x := by
  simp only [classicalPLaplacian,comparison_gradient_neg,norm_neg,
    comparison_normalizedPLaplacian_neg,mul_neg]
end BMCompactAnalytic
namespace BMCompactPDE

/-- The actual nonlinear source equation changes source sign under negation. -/
theorem WeakPSourcePair.neg_source
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) :
    WeakPSourcePair p (-c) Ω (-u) (-g) := by
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    simpa only [neg_one_smul] using (hu.2.2.1 D hD).smul (-1)
  · intro D hD θ h hθ
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
    have hf : fluxPairing p (-g) h = -fluxPairing p g h := by
      funext x
      simp only [fluxPairing,Pi.neg_apply,pFlux_neg,inner_neg_left]
    rw [hf]
    refine ⟨hi.neg,?_⟩
    simp only [Pi.neg_apply]
    rw [integral_neg,he,neg_mul]

/-- The true constant-source inequality at a local non-strict lower contact.
Only continuity of the actual weak representative is assumed. -/
theorem WeakPSourceSupersolutionPair.source_le_at_local_lower_test
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSupersolutionPair p c Ω u g)
    (huc : ContinuousOn u Ω) (hn : 2≤n)
    {x : Space n} (hx : x∈Ω) {φ : Space n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (htouch : u x=φ x)
    (hbelow : ∀ᶠ y in 𝓝 x,φ y≤u y) (hg : gradient φ x≠0) :
    c≤-BMCompactAnalytic.classicalPLaplacian p φ x := by
  obtain ⟨U,hUn,hφU⟩ := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  obtain ⟨T,hTbelow,hT,hxT⟩ := mem_nhds_iff.mp hbelow
  let D : Set (Space n) := Ω ∩ V ∩ T
  have hD : IsOpen D := (hu.2.1.inter hV).inter hT
  have hxD : x∈D := ⟨⟨hx,hxV⟩,hxT⟩
  have hDΩ : D⊆Ω := inter_subset_left.trans inter_subset_left
  have hDU : D⊆U := (inter_subset_left.trans inter_subset_right).trans hVU
  exact (hu.mono hDΩ hD).le_neg_classicalPLaplacian_at_nonstrict_contact
    (huc.mono hDΩ) hn hxD (hφU.mono hDU) htouch (fun y hy => hTbelow hy.2) hg

/-- The actual weak source equation implies the true local noncritical upper
viscosity inequality, with the correct minus-div source sign. -/
theorem WeakPSourcePair.source_ge_at_local_upper_test
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (huc : ContinuousOn u Ω) (hn : 2≤n)
    {x : Space n} (hx : x∈Ω) {φ : Space n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (htouch : u x=φ x)
    (habove : ∀ᶠ y in 𝓝 x,u y≤φ y) (hg : gradient φ x≠0) :
    -BMCompactAnalytic.classicalPLaplacian p φ x≤c := by
  have hnegative : gradient (-φ) x≠0 := by
    simpa only [BMCompactAnalytic.comparison_gradient_neg,neg_ne_zero] using hg
  have he := hu.neg_source.supersolution.source_le_at_local_lower_test huc.neg hn hx
    hφ.neg (congrArg Neg.neg htouch) (habove.mono (fun _ h => neg_le_neg h)) hnegative
  change -c ≤ -BMCompactAnalytic.classicalPLaplacian p (-φ) x at he
  rw [BMCompactAnalytic.classicalPLaplacian_neg,neg_neg] at he
  linarith only [he]

/-- A continuous source-viscosity representative and both noncritical test
inequalities are constructed from the raw actual PDE, at 1<p<n. -/
theorem WeakPSourcePair.exists_continuous_source_viscosity_representative
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ)) (hn : 2≤n) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g ∧
      (∀ x∈Ω,∀ φ : Space n → ℝ,ContDiffAt ℝ 2 φ x → v x=φ x →
        (∀ᶠ y in 𝓝 x,φ y≤v y) → gradient φ x≠0 →
          c≤-BMCompactAnalytic.classicalPLaplacian p φ x) ∧
      (∀ x∈Ω,∀ φ : Space n → ℝ,ContDiffAt ℝ 2 φ x → v x=φ x →
        (∀ᶠ y in 𝓝 x,v y≤φ y) → gradient φ x≠0 →
          -BMCompactAnalytic.classicalPLaplacian p φ x≤c) := by
  obtain ⟨v,hvc,hae,hv⟩ := hu.exists_continuous_weak_representative hpn
  refine ⟨v,hvc,hae,hv,?_,?_⟩
  · intro x hx φ hφ ht hb hg
    exact hv.supersolution.source_le_at_local_lower_test hvc hn hx hφ ht hb hg
  · intro x hx φ hφ ht ha hg
    exact hv.source_ge_at_local_upper_test hvc hn hx hφ ht ha hg

/-- The actual Dirichlet solution, genuine W0 boundary correction, interior
continuity and both noncritical source-viscosity inequalities are constructed.
Boundary continuity, C1 and general critical-point comparison remain separate. -/
theorem exists_continuous_source_viscosity_Dirichlet
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n : ℝ)) (hn : 2≤n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (c : ℝ) {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u Ω ∧ ZeroBoundarySobolevPair p Ω (u-f) (g-gf) ∧
      WeakPSourcePair p c Ω u g ∧
      (∀ x∈Ω,∀ φ : Space n → ℝ,ContDiffAt ℝ 2 φ x → u x=φ x →
        (∀ᶠ y in 𝓝 x,φ y≤u y) → gradient φ x≠0 →
          c≤-BMCompactAnalytic.classicalPLaplacian p φ x) ∧
      (∀ x∈Ω,∀ φ : Space n → ℝ,ContDiffAt ℝ 2 φ x → u x=φ x →
        (∀ᶠ y in 𝓝 x,u y≤φ y) → gradient φ x≠0 →
          -BMCompactAnalytic.classicalPLaplacian p φ x≤c) := by
  obtain ⟨u,g,huc,hb,hu,-⟩ := exists_unique_continuous_source_Dirichlet hp hpn hn hΩ hΩb c hf
  refine ⟨u,g,huc,hb,hu,?_,?_⟩
  · intro x hx φ hφ ht hl hg
    exact hu.supersolution.source_le_at_local_lower_test huc hn hx hφ ht hl hg
  · intro x hx φ hφ ht ha hg
    exact hu.source_ge_at_local_upper_test huc hn hx hφ ht ha hg

end BMCompactPDE
#print axioms BMCompactAnalytic.classicalPLaplacian_neg
#print axioms BMCompactPDE.WeakPSourcePair.neg_source
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.source_le_at_local_lower_test
#print axioms BMCompactPDE.WeakPSourcePair.source_ge_at_local_upper_test
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_source_viscosity_representative
#print axioms BMCompactPDE.exists_continuous_source_viscosity_Dirichlet
