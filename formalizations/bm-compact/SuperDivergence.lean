import SuperComparison

/-! Genuine full-W0 integration by parts for a C1 flux with continuous
actual divergence. Density is used as an identity, so the smooth approximants
need not preserve positivity. Actual classical nonpositive p-Laplacian then
implies the existing weak supersolution predicate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal NNReal
namespace BMCompactPDE

theorem inner_integrable_of_dual_memLp {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P Q : ℝ≥0∞} [ENNReal.HolderConjugate P Q] {μ : Measure α}
    {F h : α → E} (hF : MemLp F P μ) (hh : MemLp h Q μ) :
    Integrable (fun x => inner ℝ (F x) (h x)) μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.of_bilin (fun a b : E => inner ℝ a b) (1 : ℝ≥0) hF hh
    (hF.1.inner hh.1) (Eventually.of_forall (fun x => by
      simpa only [one_mul] using nnnorm_inner_le_nnnorm (𝕜 := ℝ) (F x) (h x)))

theorem tendsto_integral_inner_of_eLpNorm_sub_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P Q : ℝ≥0∞} [ENNReal.HolderConjugate P Q] {μ : Measure α}
    {F h : α → E} {g : ℕ → α → E}
    (hF : MemLp F P μ) (hh : MemLp h Q μ) (hg : ∀ j, MemLp (g j) Q μ)
    (hlim : Tendsto (fun j => eLpNorm (g j-h) Q μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, inner ℝ (F x) (g j x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F x) (h x) ∂μ)) := by
  have hint := inner_integrable_of_dual_memLp hF hh
  have hintg (j : ℕ) := inner_integrable_of_dual_memLp hF (hg j)
  have hb (j : ℕ) :
      eLpNorm ((fun x => inner ℝ (F x) (g j x))-(fun x => inner ℝ (F x) (h x))) 1 μ ≤
      eLpNorm F P μ*eLpNorm (g j-h) Q μ := by
    have hineq := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (p := P) (q := Q) (r := 1) hF.1 ((hg j).sub hh).1
      (fun a b : E => inner ℝ a b) (1 : ℝ≥0)
      (Eventually.of_forall (fun x => by
        simpa only [NNReal.coe_one,one_mul,Pi.sub_apply] using
          norm_inner_le_norm (𝕜 := ℝ) (F x) (g j x-h x)))
    simpa only [ENNReal.coe_one,one_mul,Pi.sub_def,inner_sub_right] using hineq
  have hboundlim : Tendsto (fun j => eLpNorm F P μ*eLpNorm (g j-h) Q μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hF.eLpNorm_ne_top)
  have hL1 := tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hboundlim (fun _ => bot_le) hb
  exact tendsto_integral_of_L1' _ hint.1 (Eventually.of_forall hintg) hL1

/-- Full-W0 C1 flux integration by parts, derived by simultaneous Lp limits
of the actual functions and their actual gradient approximants. -/
theorem integral_inner_eq_neg_divergence_zeroBoundary_one
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω D : Set (Space n)}
    (hΩ : IsOpen Ω) (hD : LocalDomain D Ω)
    {F : Space n → Space n} (hF : ContDiffOn ℝ 1 F Ω)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p D θ h) :
    Integrable (fun x => inner ℝ (F x) (h x)) (volume.restrict D) ∧
    Integrable (fun x => coordinateDivergence F x*θ x) (volume.restrict D) ∧
      (∫ x in D, inner ℝ (F x) (h x)) = -(∫ x in D, coordinateDivergence F x*θ x) := by
  haveI := holderConjugate_p_dual hp
  let Q := ENNReal.ofReal (p/(p-1))
  have hFQ : MemLp F Q (volume.restrict D) :=
    memLp_on_bounded_of_continuousOn_closure Q hD.2.1 hD.1.measurableSet
      (hF.continuousOn.mono hD.2.2)
  have hbQ : MemLp (coordinateDivergence F) Q (volume.restrict D) :=
    memLp_on_bounded_of_continuousOn_closure Q hD.2.1 hD.1.measurableSet
      ((continuousOn_coordinateDivergence_of_contDiffOn_one hΩ hF).mono hD.2.2)
  obtain ⟨hSob,φ,hφ,hLu,hLg⟩ := hθ
  have hφSob (j : ℕ) := (hφ j).sobolevPair hp
  have hiF := inner_integrable_of_dual_memLp hFQ hSob.2.2.1
  have hib : Integrable (fun x => coordinateDivergence F x*θ x) (volume.restrict D) := by
    simpa only [Real.inner_apply,mul_comm] using inner_integrable_of_dual_memLp hbQ hSob.2.1
  have htF := tendsto_integral_inner_of_eLpNorm_sub_zero hFQ hSob.2.2.1
    (fun j => (hφSob j).2.2.1) hLg
  have htb : Tendsto (fun j => ∫ x in D, coordinateDivergence F x*φ j x) atTop
      (𝓝 (∫ x in D, coordinateDivergence F x*θ x)) := by
    simpa only [Real.inner_apply,mul_comm] using
      tendsto_integral_inner_of_eLpNorm_sub_zero hbQ hSob.2.1
        (fun j => (hφSob j).2.1) hLu
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have hcoord (i : Fin n) : ContDiffOn ℝ 1 (fun x => F x i) D :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (hF.mono hDΩ)
  have heq (j : ℕ) : (∫ x in D, inner ℝ (F x) (gradient (φ j) x)) =
      -(∫ x in D, coordinateDivergence F x*φ j x) :=
    (integral_inner_gradient_eq_neg_divergence_one hD.1 hcoord (hφ j)).2.2
  refine ⟨hiF,hib,?_⟩
  exact tendsto_nhds_unique htF (htb.neg.congr' (Eventually.of_forall (fun j => (heq j).symm)))

/-- A genuine C1 nonlinear flux with nonpositive actual divergence satisfies
the full concrete weak supersolution inequality. No inequality for W0 tests
is supplied as a premise. -/
theorem weakPSupersolutionPair_of_divergence_nonpos_one
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (hF : ContDiffOn ℝ 1 (fun x => pFlux p (g x)) Ω)
    (hdiv : ∀ x∈Ω, coordinateDivergence (fun y => pFlux p (g y)) x≤0) :
    WeakPSupersolutionPair p Ω u g := by
  refine ⟨hp,hΩ,hSob,?_⟩
  intro D hD θ h hθ hθ0
  obtain ⟨hiF,hib,heq⟩ := integral_inner_eq_neg_divergence_zeroBoundary_one hp hΩ hD hF hθ
  refine ⟨hiF,?_⟩
  change 0≤∫ x in D, inner ℝ (pFlux p (g x)) (h x)
  rw [heq]
  apply neg_nonneg.mpr
  apply integral_nonpos_of_ae
  filter_upwards [hθ0,ae_restrict_mem hD.1.measurableSet] with x hx0 hx
  exact mul_nonpos_of_nonpos_of_nonneg (hdiv x (hD.2.2 (subset_closure hx))) hx0

/-- The actual classical Hessian inequality yields the actual weak
supersolution predicate in the noncritical C2 test-function subcase. -/
theorem weakPSupersolutionPair_of_classicalPLaplacian_nonpos
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hg : ∀ x∈Ω, gradient u x≠0)
    (hP : ∀ x∈Ω, BMCompactAnalytic.classicalPLaplacian p u x≤0) :
    WeakPSupersolutionPair p Ω u (gradient u) := by
  have hf := contDiffOn_pFlux_gradient_of_contDiffOn_two p hΩ hu hg
  apply weakPSupersolutionPair_of_divergence_nonpos_one hp hΩ
    (locallySobolevPair_of_contDiffOn_one hp hΩ (hu.of_le (by norm_num))) hf
  intro x hx
  have hd := (hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  unfold coordinateDivergence
  rw [←classicalDivergence_eq_sum_gradient_coordinates hd,
    classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
      (hu.contDiffAt (hΩ.mem_nhds hx)) (hg x hx)]
  exact hP x hx

end BMCompactPDE
#print axioms BMCompactPDE.inner_integrable_of_dual_memLp
#print axioms BMCompactPDE.tendsto_integral_inner_of_eLpNorm_sub_zero
#print axioms BMCompactPDE.integral_inner_eq_neg_divergence_zeroBoundary_one
#print axioms BMCompactPDE.weakPSupersolutionPair_of_divergence_nonpos_one
#print axioms BMCompactPDE.weakPSupersolutionPair_of_classicalPLaplacian_nonpos
