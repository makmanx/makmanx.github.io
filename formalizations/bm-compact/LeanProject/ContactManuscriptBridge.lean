import BMCompactCriticalChecked

/-! The exact manuscript strict global test convention implies the stronger
local convention for a function with an actual global upper bound on its
domain. A genuine smooth cutoff patches a local C2 test to a global C2 test;
a quartic gives strict contact and preserves the actual first two derivatives.
No weak equation or regularity of the viscosity function is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactAnalytic

theorem normalizedPLaplacian_eq_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (p : ℝ) {f g : E → ℝ} {x : E} (heq : f =ᶠ[𝓝 x] g) :
    normalizedPLaplacian p f x=normalizedPLaplacian p g x := by
  have hg : gradient f x=gradient g x := by
    unfold gradient
    rw [heq.fderiv_eq]
  have hH : actualHessian f x=actualHessian g x := heq.fderiv.fderiv_eq
  simp only [normalizedPLaplacian,actualLaplacian,actualHessianEnd,hg,hH]

theorem IsManuscriptViscosityPSubsolution.local_of_boundedAbove
    {n : ℕ} {p M : ℝ} {Ω : Set (BMCompactPDE.Space n)}
    {u : BMCompactPDE.Space n → ℝ}
    (hu : IsManuscriptViscosityPSubsolution p Ω u)
    (hub : ∀ y∈Ω, u y≤M) : IsViscosityPSubsolution p Ω u := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro x hx φ hφ hvalue hupper hgφ
  obtain ⟨U,hUn,hφU⟩ := hφ.contDiffOn le_rfl (by simp)
  have hN : Ω ∩ (U ∩ {y | u y≤φ y})∈𝓝 x :=
    inter_mem (hu.2.1.mem_nhds hx) (inter_mem hUn hupper)
  obtain ⟨V,hVsub,hVopen,hxV⟩ := _root_.mem_nhds_iff.mp hN
  have hφV : ContDiffOn ℝ 2 φ V := hφU.mono (fun y hy => (hVsub hy).2.1)
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hVopen x hxV
  let R : ℝ := η/2
  have hR : 0<R := half_pos hη
  have hRη : R<η := half_lt_self hη
  let K : Set (BMCompactPDE.Space n) := closedBall x R
  have hKV : K ⊆ V := by
    intro y hy
    exact hηV (lt_of_le_of_lt (mem_closedBall.mp hy) hRη)
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact
    (isCompact_closedBall x R) hVopen hKV
  let χ : BMCompactPDE.Space n → ℝ := fun y => Real.smoothTransition (f y)
  have hχcd : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hχs : tsupport χ ⊆ V :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) f).trans hf.2.2.1
  have hχ0 (y : BMCompactPDE.Space n) : 0≤χ y := Real.smoothTransition.nonneg _
  have hχle (y : BMCompactPDE.Space n) : χ y≤1 := Real.smoothTransition.le_one _
  have hχ1 (y : BMCompactPDE.Space n) (hy : y∈K) : χ y=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 y hy)
  let b : BMCompactPDE.Space n → ℝ := fun y => χ y*φ y+(1-χ y)*(M+1)
  have hχ2 : ContDiff ℝ 2 χ := hχcd.of_le (by decide)
  have hprod : ContDiff ℝ 2 (fun y => χ y*φ y) :=
    BMCompactPDE.contDiff_of_contDiffOn_tsupport_subset hVopen
      (hχ2.contDiffOn.mul hφV) (tsupport_mul_subset_left.trans hχs)
  have hb : ContDiff ℝ 2 b := hprod.add ((contDiff_const.sub hχ2).mul contDiff_const)
  have hbupper : ∀ y∈Ω, u y≤b y := by
    intro y hy
    by_cases hys : y∈tsupport χ
    · have hloc := (hVsub (hχs hys)).2.2
      have hM := hub y hy
      have hp1 := mul_nonneg (hχ0 y) (sub_nonneg.mpr hloc)
      have hp2 := mul_nonneg (sub_nonneg.mpr (hχle y))
        (by linarith : 0≤M+1-u y)
      dsimp only [b]
      nlinarith
    · have hz : χ y=0 := image_eq_zero_of_notMem_tsupport hys
      dsimp only [b]
      rw [hz,zero_mul,sub_zero,one_mul,zero_add]
      linarith [hub y hy]
  have heq : b =ᶠ[𝓝 x] φ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with y hy
    have hχy := hχ1 y (mem_closedBall.mpr (mem_ball.mp hy).le)
    dsimp only [b]
    rw [hχy,one_mul,sub_self,zero_mul,add_zero]
  have hbx : b x=φ x := by
    have hχx := hχ1 x (mem_closedBall_self hR.le)
    dsimp only [b]
    rw [hχx,one_mul,sub_self,zero_mul,add_zero]
  let ψ : BMCompactPDE.Space n → ℝ := fun y => b y+strictContactQuartic x y
  have hq : ContDiff ℝ 2 (strictContactQuartic x : BMCompactPDE.Space n → ℝ) :=
    (contDiff_strictContactQuartic x).of_le (by decide)
  have hψ : ContDiff ℝ 2 ψ := hb.add hq
  have hvalueψ : u x=ψ x := by
    change u x=b x+strictContactQuartic x x
    rw [hbx,strictContactQuartic_self,add_zero]
    exact hvalue
  have hstrict : ∀ y∈Ω, y≠x → u y<ψ y := by
    intro y hy hne
    have hl := hbupper y hy
    have hp := strictContactQuartic_pos hne
    change u y<b y+strictContactQuartic x y
    linarith
  have hgb : gradient b x=gradient φ x := by
    unfold gradient
    rw [heq.fderiv_eq]
  have hgψ : gradient ψ x≠0 := by
    change gradient (fun y => b y+strictContactQuartic x y) x≠0
    rw [gradient_add_strictContactQuartic_self (hb.differentiable (by norm_num) x),hgb]
    exact hgφ
  have hi := hu.2.2.2 x hx ψ hψ.contDiffOn hvalueψ hstrict hgψ
  change 0≤normalizedPLaplacian p (fun y => b y+strictContactQuartic x y) x at hi
  rw [normalizedPLaplacian_add_strictContactQuartic_self p hb.contDiffAt,
    normalizedPLaplacian_eq_of_eventuallyEq p heq] at hi
  exact hi

end BMCompactAnalytic
#print axioms BMCompactAnalytic.normalizedPLaplacian_eq_of_eventuallyEq
#print axioms BMCompactAnalytic.IsManuscriptViscosityPSubsolution.local_of_boundedAbove
