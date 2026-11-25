import GradientHessianActual
import ComparisonSelectedDirichlet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Actual linear constant-source weak equations differentiate to homogeneous
weak equations for the supplied gradient components. The weak Hessian is
constructed from the genuine p=2 regularized equation, not assumed.
No differentiability or harmonicity of the gradient is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff BigOperators
namespace BMCompactPDE

private def comparisonPartial {n : ℕ} (φ : Space n → ℝ) (i : Fin n) : Space n → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i)

private theorem comparisonPartial_eq_gradient {n : ℕ} (φ : Space n → ℝ)
    (i : Fin n) (x : Space n) : comparisonPartial φ i x=(gradient φ x) i :=
  (gradient_coordinate_eq_fderiv φ x i).symm

private theorem comparisonPartial_smoothTest {n : ℕ} {D : Set (Space n)}
    {φ : Space n → ℝ} (hφ : SmoothTest D φ) (i : Fin n) :
    SmoothTest D (comparisonPartial φ i) := by
  refine ⟨?_,hφ.2.1.fderiv_apply ℝ _,?_⟩
  · exact (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2

private theorem comparisonPartial_commute {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) (x : Space n) :
    comparisonPartial (comparisonPartial φ i) j x=
      comparisonPartial (comparisonPartial φ j) i x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by decide)).differentiable (by norm_num) x
  have hi := fderiv_clm_apply hfd
    (differentiableAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ i))
  have hj := fderiv_clm_apply hfd
    (differentiableAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ j))
  change (fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i)) x)
      (EuclideanSpace.basisFun (Fin n) ℝ j)=
    (fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ j)) x)
      (EuclideanSpace.basisFun (Fin n) ℝ i)
  rw [hi,hj]
  simpa only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply] using
      (hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by
          simpa only [minSmoothness_of_isRCLikeNormedField] using
            (show (2 : ℕ∞ω)≤(∞ : ℕ∞ω) by decide))
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i)

private theorem comparison_weak_gradient_curl_pairing {n : ℕ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n} (hu : HasWeakGradientOn D u g)
    {φ : Space n → ℝ} (hφ : SmoothTest D φ) (i j : Fin n) :
    (∫ x in D,g x i*comparisonPartial φ j x)=
      ∫ x in D,g x j*comparisonPartial φ i x := by
  have hi := (hu (comparisonPartial φ j) (comparisonPartial_smoothTest hφ j) i).2.2
  have hj := (hu (comparisonPartial φ i) (comparisonPartial_smoothTest hφ i) j).2.2
  have he : (fun x => u x*(gradient (comparisonPartial φ j) x) i)=
      (fun x => u x*(gradient (comparisonPartial φ i) x) j) := by
    funext x
    rw [←comparisonPartial_eq_gradient,←comparisonPartial_eq_gradient,
      comparisonPartial_commute hφ.1 j i x]
  rw [he] at hi
  linarith only [hi,hj]

private theorem comparison_integral_partial_zero {n : ℕ} {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) {φ : Space n → ℝ}
    (hφ : SmoothTest D φ) (i : Fin n) : (∫ x in D,comparisonPartial φ i x)=0 := by
  have hh := ((sobolevPair_const (by norm_num : (1:ℝ)<2) hDb 1).2.2.2 φ hφ i).2.2
  simpa only [Pi.zero_apply,PiLp.zero_apply,zero_mul,one_mul,integral_zero,neg_zero,
    comparisonPartial_eq_gradient] using hh

/-- The p=2 regularized flux is the original linear flux. The full global weak
regularized equation is derived from the actual local source equation. -/
theorem WeakPSourcePair.global_regularized_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : WeakPSourcePair 2 c Ω u g)
    (hSob : SobolevPair 2 Ω u g) (hΩb : Bornology.IsBounded Ω) (ε : ℝ) :
    GlobalWeakRegularizedSourcePair 2 ε c Ω u g := by
  refine ⟨by norm_num,hu.2.1,hSob,?_⟩
  intro θ h hθ
  obtain ⟨hi,_,he⟩ := hu.integral_eq_global hΩb hSob hθ
  have hflux : fluxPairing 2 g h=(fun x => inner ℝ (g x) (h x)) := by
    funext x
    simp only [fluxPairing,pFlux,sub_self,Real.rpow_zero,one_smul]
  rw [hflux] at hi he
  simpa only [sub_self,zero_div,Real.rpow_zero,one_smul] using And.intro hi he

/-- An actual constant-source linear solution has genuine local weak harmonic
gradient components. The weak-Hessian rows and the component PDEs are built. -/
theorem WeakPSourcePair.exists_weak_harmonic_gradient_rows_two
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hf : SobolevPair 2 Ω u g)
    (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ H : Fin n → Space n → Space n,∀ i : Fin n,
      SobolevPair 2 D (fun x => g x i) (H i) ∧
      WeakPHarmonicPair 2 D (fun x => g x i) (H i) := by
  have hreg := hu.global_regularized_two hf hΩb 1
  obtain ⟨H,hH⟩ := hreg.exists_local_sobolev_gradient_rows_ge_two
    (by norm_num) (by norm_num) hΩb hD
  have huD := hu.2.2.1 D hD
  refine ⟨H,?_⟩
  intro i
  refine ⟨hH i,?_⟩
  apply WeakPSourcePair.harmonic_of_source_zero
  apply weakPSourcePair_of_sobolev_smooth_source_equation hD.1 (hH i)
  intro φ hφ
  let ψ := comparisonPartial φ i
  have hψ : SmoothTest D ψ := comparisonPartial_smoothTest hφ i
  have hψzero : (∫ x in D,ψ x)=0 := comparison_integral_partial_zero hD.2.1 hφ i
  obtain ⟨hfluxI,hflux⟩ := hu.2.2.2 D hD ψ (gradient ψ) (hψ.zeroBoundarySobolevPair hu.1)
  have hsource : (∫ x in D,inner ℝ (g x) (gradient ψ x))=0 := by
    simpa only [fluxPairing,pFlux,sub_self,Real.rpow_zero,one_smul,hψzero,mul_zero] using hflux
  let L : Fin n → Space n → ℝ := fun j x => (H i x) j*comparisonPartial φ j x
  let R : Fin n → Space n → ℝ := fun j x => g x j*comparisonPartial ψ j x
  have hL (j : Fin n) : Integrable (L j) (volume.restrict D) := by
    exact ((hH i).2.2.2 (comparisonPartial φ j) (comparisonPartial_smoothTest hφ j) j).2.1
  have hR (j : Fin n) : Integrable (R j) (volume.restrict D) := by
    exact (huD.2.2.2 (comparisonPartial ψ j) (comparisonPartial_smoothTest hψ j) j).2.1
  have hLR (j : Fin n) : (∫ x in D,L j x)=-(∫ x in D,R j x) := by
    have he := ((hH i).2.2.2 (comparisonPartial φ j) (comparisonPartial_smoothTest hφ j) j).2.2
    have he' : (∫ x in D,g x i*comparisonPartial (comparisonPartial φ j) j x)=
        -(∫ x in D,L j x) := by
      simpa only [comparisonPartial_eq_gradient,L] using he
    have hcurl := comparison_weak_gradient_curl_pairing huD.2.2.2 (comparisonPartial_smoothTest hφ j) i j
    have hcomm : (fun x => g x j*comparisonPartial (comparisonPartial φ j) i x)=R j := by
      funext x
      dsimp only [R,ψ]
      rw [comparisonPartial_commute hφ.1 j i x]
    rw [hcomm] at hcurl
    change _=∫ x in D,R j x at hcurl
    linarith only [he',hcurl]
  have hLi : (fun x => inner ℝ (H i x) (gradient φ x))=fun x => ∑ j : Fin n,L j x := by
    funext x
    simp only [L,PiLp.inner_apply,Real.inner_apply,comparisonPartial_eq_gradient]
  have hRi : (fun x => inner ℝ (g x) (gradient ψ x))=fun x => ∑ j : Fin n,R j x := by
    funext x
    simp only [R,PiLp.inner_apply,Real.inner_apply,comparisonPartial_eq_gradient]
  have hzero : (∫ x in D,inner ℝ (H i x) (gradient φ x))=0 := by
    rw [hLi,integral_finsetSum Finset.univ (fun j _ => hL j)]
    rw [hRi,integral_finsetSum Finset.univ (fun j _ => hR j)] at hsource
    calc
      _=∑ j : Fin n,-(∫ x in D,R j x) := Finset.sum_congr rfl (fun j _ => hLR j)
      _=-(∑ j : Fin n,∫ x in D,R j x) := Finset.sum_neg_distrib _
      _=0 := by rw [hsource,neg_zero]
  simpa only [fluxPairing,pFlux,sub_self,Real.rpow_zero,one_smul,zero_mul] using hzero

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.global_regularized_two
#print axioms BMCompactPDE.WeakPSourcePair.exists_weak_harmonic_gradient_rows_two
