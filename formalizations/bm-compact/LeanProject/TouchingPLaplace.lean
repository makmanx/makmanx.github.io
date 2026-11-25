import TouchingSecondCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

/-! The actual classical normalized p-Laplace upper-test inequality of printed
Lemma4.3 (source lem5.3). This is a pointwise C² result. The weak-PDE regularity,
noncritical-pair existence, and viscosity-comparison bridges remain separate. -/
noncomputable section
set_option autoImplicit false
open Filter Set InnerProductSpace
open scoped Topology ContDiff BigOperators
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Riesz endomorphism of the actual second Fréchet derivative. -/
def actualHessianEnd (f : E → ℝ) (x : E) : E →ₗ[ℝ] E :=
  (toDual ℝ E).symm.toLinearMap.comp (actualHessian f x).toLinearMap

/-- The Laplacian is the trace of the actual Hessian endomorphism. -/
def actualLaplacian (f : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E (actualHessianEnd f x)

/-- Actual normalized classical p-Laplacian, at noncritical points. -/
def normalizedPLaplacian (p : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  actualLaplacian f x + (p-2) * (‖gradient f x‖^2)⁻¹ *
    actualHessian f x (gradient f x) (gradient f x)

/-- Classical p-Laplace Hessian formula; weak/divergence identification is a
separate theorem and is not assumed silently in the results below. -/
def classicalPLaplacian (p : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ‖gradient f x‖ ^ (p-2) * normalizedPLaplacian p f x

omit [FiniteDimensional ℝ E] in
/-- The actual trace is the diagonal Hessian sum in every orthonormal basis. -/
theorem actualLaplacian_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) :
    actualLaplacian f x = ∑ i, actualHessian f x (b i) (b i) := by
  classical
  rw [actualLaplacian, LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  change (∑ i, (LinearMap.toMatrix b.toBasis b.toBasis (actualHessianEnd f x)) i i) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, b.repr_apply_apply]
  change inner ℝ (b i) ((toDual ℝ E).symm (actualHessian f x (b i))) = _
  rw [real_inner_comm, ←toDual_apply_apply, (toDual ℝ E).apply_symm_apply]

omit [CompleteSpace E] in
/-- A unit vector belongs to an actual orthonormal basis of the ambient space. -/
theorem exists_orthonormalBasis_containing {ν : E} (hν : ‖ν‖=1) :
    ∃ (s : Finset E) (b : OrthonormalBasis s ℝ E) (i₀ : s), b i₀ = ν := by
  classical
  have hs : Orthonormal ℝ ((↑) : ({ν} : Set E) → E) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : E) = ν := Set.mem_singleton_iff.mp i.property
    have hj : (j : E) = ν := Set.mem_singleton_iff.mp j.property
    have hij : i=j := Subtype.ext (hi.trans hj.symm)
    rw [if_pos hij,hi,hj,real_inner_self_eq_norm_sq,hν]
    norm_num
  obtain ⟨s,b,hsb,hb⟩ := hs.exists_orthonormalBasis_extension
  have hmem : ν ∈ s := hsb (by simp)
  refine ⟨s,b,⟨ν,hmem⟩,?_⟩
  rw [hb]

omit [FiniteDimensional ℝ E] in
/-- The common-gradient expression for the actual normalized p-Laplacian. -/
theorem normalizedPLaplacian_eq_aligned {p a : ℝ} {f : E → ℝ} {x ν : E}
    (ha : 0<a) (hν : ‖ν‖=1) (hg : gradient f x = (-a) • ν) :
    normalizedPLaplacian p f x =
      actualLaplacian f x + (p-2)*actualHessian f x ν ν := by
  unfold normalizedPLaplacian
  rw [hg,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha,hν,mul_one]
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp

omit [FiniteDimensional ℝ E] in
/-- At a noncritical point, the actual classical Hessian formula vanishes
only if the normalized formula vanishes. -/
theorem normalizedPLaplacian_eq_zero_of_classical_eq_zero {p : ℝ}
    {f : E → ℝ} {x : E} (hg : gradient f x ≠ 0)
    (hP : classicalPLaplacian p f x = 0) : normalizedPLaplacian p f x = 0 := by
  have hpos : 0 < ‖gradient f x‖ ^ (p-2) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hg) _
  exact (mul_eq_zero.mp hP).resolve_left hpos.ne'

/-- The elliptic trace uses positive weights 1 and p-1 even for 1<p<2. -/
theorem elliptic_weighted_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (p : ℝ) (r : ι → ℝ) :
    (∑ i, (if i=i₀ then p-1 else 1) * r i) =
      (∑ i, r i) + (p-2)*r i₀ := by
  have heq (i : ι) : (if i=i₀ then p-1 else 1) * r i =
      r i + (if i=i₀ then (p-2)*r i else 0) := by
    split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simp

/-- Positive elliptic trace applied to the actual cubic Hessian comparison.
No symmetry or sign assumption on the individual Hessians is required. -/
theorem aligned_normalizedPLaplacian_comparison {p c₁ c₂ : ℝ}
    (hp : 1<p) {v₁ v₂ φ : E → ℝ} {y z x ν : E}
    {a b d : ℝ} (ha : 0<a) (hb : 0<b) (hd : 0<d) (hν : ‖ν‖=1)
    (hg₁ : gradient v₁ y = (-a) • ν) (hg₂ : gradient v₂ z = (-b) • ν)
    (hgφ : gradient φ x = (-d) • ν)
    (hH : ∀ e : E, c₁*actualHessian v₁ y e e + c₂*actualHessian v₂ z e e ≤
      actualHessian φ x e e) :
    c₁*normalizedPLaplacian p v₁ y + c₂*normalizedPLaplacian p v₂ z ≤
      normalizedPLaplacian p φ x := by
  classical
  obtain ⟨s,basis,i₀,hi₀⟩ := exists_orthonormalBasis_containing hν
  let w : s → ℝ := fun i => if i=i₀ then p-1 else 1
  have hw (i : s) : 0 ≤ w i := by
    dsimp [w]
    split_ifs <;> linarith
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hH (basis i)) (hw i))
  have hsum (f : E → ℝ) (q : E) :
      (∑ i, w i * actualHessian f q (basis i) (basis i)) =
        actualLaplacian f q + (p-2)*actualHessian f q ν ν := by
    rw [show w = (fun i => if i=i₀ then p-1 else 1) from rfl]
    rw [elliptic_weighted_sum, ←actualLaplacian_eq_sum basis f q,hi₀]
  have hlinear :
      (∑ i, w i * (c₁*actualHessian v₁ y (basis i) (basis i) +
        c₂*actualHessian v₂ z (basis i) (basis i))) =
      c₁*(∑ i, w i*actualHessian v₁ y (basis i) (basis i)) +
        c₂*(∑ i, w i*actualHessian v₂ z (basis i) (basis i)) := by
    calc
      _ = ∑ i, (c₁*(w i*actualHessian v₁ y (basis i) (basis i)) +
          c₂*(w i*actualHessian v₂ z (basis i) (basis i))) :=
        Finset.sum_congr rfl (fun i hi => by ring)
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
  rw [hlinear,hsum v₁ y,hsum v₂ z,hsum φ x] at hs
  rw [normalizedPLaplacian_eq_aligned ha hν hg₁,
    normalizedPLaplacian_eq_aligned hb hν hg₂,
    normalizedPLaplacian_eq_aligned hd hν hgφ]
  exact hs

/-- Printed Lemma4.3's local normalized p-Laplace test inequality. Endpoint
C² regularity and the actual classical equations are explicit premises;
neither weak-PDE regularity nor a viscosity comparison principle is postulated. -/
theorem local_touching_normalizedPLaplacian_nonneg {p t : ℝ}
    (hp : 1<p) (ht : 0<t) (ht1 : t<1) {v₁ v₂ φ : E → ℝ} {y z x : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : ContDiffAt ℝ 2 v₁ y) (h₂ : ContDiffAt ℝ 2 v₂ z)
    (hφ : ContDiffAt ℝ 2 φ x)
    (hg₁ : gradient v₁ y ≠ 0) (hg₂ : gradient v₂ z ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2))
    (hP₁ : classicalPLaplacian p v₁ y = 0)
    (hP₂ : classicalPLaplacian p v₂ z = 0) :
    gradient φ x ≠ 0 ∧ 0 ≤ normalizedPLaplacian p φ x := by
  obtain ⟨ν,a,b,d,hν,ha,hb,hd,hgA,hgB,hgD,hrec,hH⟩ :=
    local_touching_gradient_and_hessian ht ht1 hx h₁ h₂ hφ hg₁ hg₂ hv₁ hv₂ htouch
  have hgφ : gradient φ x ≠ 0 := by
    intro hz
    have hh := congrArg norm hgD
    rw [hz,norm_zero,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hd,hν,mul_one] at hh
    linarith
  refine ⟨hgφ,?_⟩
  have hbnd := aligned_normalizedPLaplacian_comparison hp ha hb hd hν hgA hgB hgD hH
  rw [normalizedPLaplacian_eq_zero_of_classical_eq_zero hg₁ hP₁,
    normalizedPLaplacian_eq_zero_of_classical_eq_zero hg₂ hP₂] at hbnd
  simpa using hbnd

/-- In Euclidean coordinates, the actual trace is the standard orthonormal
coordinate sum of actual second derivatives. -/
theorem actualLaplacian_euclidean_eq_sum {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    actualLaplacian f x = ∑ i : Fin n, actualHessian f x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) :=
  actualLaplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) f x

end BMCompactAnalytic
#print axioms BMCompactAnalytic.actualLaplacian_eq_sum
#print axioms BMCompactAnalytic.exists_orthonormalBasis_containing
#print axioms BMCompactAnalytic.normalizedPLaplacian_eq_aligned
#print axioms BMCompactAnalytic.normalizedPLaplacian_eq_zero_of_classical_eq_zero
#print axioms BMCompactAnalytic.elliptic_weighted_sum
#print axioms BMCompactAnalytic.aligned_normalizedPLaplacian_comparison
#print axioms BMCompactAnalytic.local_touching_normalizedPLaplacian_nonneg
#print axioms BMCompactAnalytic.actualLaplacian_euclidean_eq_sum
