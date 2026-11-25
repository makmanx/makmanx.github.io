import OuterNeighborhoodPotential
import CapacityBoundaryAEUniqueness
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem rigid_decomp {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    (e : Space n → Space n) = fun x => e.linearIsometryEquiv x + e 0 := by
  funext x
  simpa using e.map_vadd 0 x

theorem rigid_measurePreserving {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    MeasurePreserving e volume volume := by
  rw [rigid_decomp e]
  exact (measurePreserving_add_right volume (e 0)).comp e.linearIsometryEquiv.measurePreserving

private theorem rigid_hasFDerivAt {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) (x : Space n) :
    HasFDerivAt e e.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap x := by
  rw [rigid_decomp e]
  exact e.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.add_const _

private theorem rigid_contDiff {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    ContDiff ℝ ∞ (e : Space n → Space n) := by
  rw [rigid_decomp e]
  exact e.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.add contDiff_const

theorem gradient_comp_rigid {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Space n) :
    gradient (f ∘ e) x = e.linearIsometryEquiv.symm (gradient f (e x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,fderiv_comp x ((hf.differentiable (by simp)).differentiableAt)
    (rigid_hasFDerivAt e x).differentiableAt,(rigid_hasFDerivAt e x).fderiv]
  change fderiv ℝ f (e x) (e.linearIsometryEquiv v) = _
  rw [←inner_gradient_left]
  exact (e.linearIsometryEquiv.symm.inner_map_eq_flip _ _).symm

theorem admissible_comp_rigid {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) {K : Set (Space n)}
    {f : Space n → ℝ} (hf : BMCompactCapacityV2.Admissible K univ f) :
    BMCompactCapacityV2.Admissible (e ⁻¹' K) univ (f ∘ e) :=
  ⟨hf.1.comp (rigid_contDiff e),hf.2.1.comp_isClosedEmbedding e.isometry.isClosedEmbedding,
    subset_univ _,fun _ hx=>hf.2.2.2 _ hx⟩

private theorem variationalCapacity_rigid_le {n : ℕ} (p : ℝ) (K : Set (Space n))
    (e : Space n ≃ᵃⁱ[ℝ] Space n) : BMCompactCapacityV2.variationalCapacity p (e ⁻¹' K) ≤
    BMCompactCapacityV2.variationalCapacity p K := by
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  apply (BMCompactCapacityV2.relativeCapacity_le_energy p (admissible_comp_rigid e hf)).trans_eq
  simp only [BMCompactCapacityV2.pEnergy,Measure.restrict_univ,gradient_comp_rigid e hf.1,
    LinearIsometryEquiv.norm_map]
  exact (rigid_measurePreserving e).lintegral_comp_emb e.isometry.isClosedEmbedding.measurableEmbedding
    (fun z => ENNReal.ofReal (‖gradient f z‖^p))

theorem variationalCapacity_rigid {n : ℕ} (p : ℝ) (K : Set (Space n))
    (e : Space n ≃ᵃⁱ[ℝ] Space n) : BMCompactCapacityV2.variationalCapacity p (e ⁻¹' K) =
    BMCompactCapacityV2.variationalCapacity p K := by
  refine le_antisymm (variationalCapacity_rigid_le p K e) ?_
  simpa [Set.preimage_preimage, Function.comp_def] using variationalCapacity_rigid_le p (e ⁻¹' K) e.symm

end BMCompactPDE
#print axioms BMCompactPDE.rigid_measurePreserving
#print axioms BMCompactPDE.admissible_comp_rigid
#print axioms BMCompactPDE.gradient_comp_rigid
#print axioms BMCompactPDE.variationalCapacity_rigid
