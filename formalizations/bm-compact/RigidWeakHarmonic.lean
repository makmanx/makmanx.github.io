import CapacityRigidMotion
import WeakDensity
import WeakGlobalTesting

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- A weak gradient gives the distributional integration formula along any
constant direction, with integrability of both sides. -/
theorem HasWeakGradientOn.directional_identity {n : ℕ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n} (hu : HasWeakGradientOn D u g)
    {φ : Space n → ℝ} (hφ : SmoothTest D φ) (v : Space n) :
    Integrable (fun x=>u x*inner ℝ (gradient φ x) v) (volume.restrict D) ∧
    Integrable (fun x=>inner ℝ (g x) v*φ x) (volume.restrict D) ∧
      (∫ x in D, u x*inner ℝ (gradient φ x) v) = -(∫ x in D, inner ℝ (g x) v*φ x) := by
  let L := fun (i : Fin n) (x : Space n)=>v i*(u x*(gradient φ x) i)
  let M := fun (i : Fin n) (x : Space n)=>v i*((g x) i*φ x)
  have h (i : Fin n) := hu φ hφ i
  have hL (i : Fin n) : Integrable (L i) (volume.restrict D) := (h i).1.const_mul _
  have hM (i : Fin n) : Integrable (M i) (volume.restrict D) := (h i).2.1.const_mul _
  have heL : (fun x=>u x*inner ℝ (gradient φ x) v)=fun x=>∑ i : Fin n,L i x := by
    funext x
    simp only [PiLp.inner_apply,Real.inner_apply,Finset.mul_sum,L]
    exact Finset.sum_congr rfl (fun i _=>by ring)
  have heM : (fun x=>inner ℝ (g x) v*φ x)=fun x=>∑ i : Fin n,M i x := by
    funext x
    simp only [PiLp.inner_apply,Real.inner_apply,Finset.sum_mul,M]
    exact Finset.sum_congr rfl (fun i _=>by ring)
  rw [heL,heM]
  refine ⟨?_,?_,?_⟩
  · exact integrable_finsetSum _ (fun i _=>hL i)
  · exact integrable_finsetSum _ (fun i _=>hM i)
  · rw [integral_finsetSum _ (fun i _=>hL i),integral_finsetSum _ (fun i _=>hM i), ←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [L,M,integral_const_mul,(h i).2.2,mul_neg]

private theorem rigid_smooth {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    ContDiff ℝ ∞ (e : Space n → Space n) := by
  have hd : (e : Space n → Space n)=fun x=>e.linearIsometryEquiv x + e 0 := by
    funext x;simpa using e.map_vadd 0 x
  rw [hd]
  exact e.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.add contDiff_const

private theorem rigid_test {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n)
    {D : Set (Space n)} {φ : Space n→ℝ} (hf : SmoothTest D φ) :
    SmoothTest (e ⁻¹' D) (φ ∘ e) := by
  refine ⟨hf.1.comp (rigid_smooth e),hf.2.1.comp_isClosedEmbedding e.isometry.isClosedEmbedding,?_⟩
  have he : tsupport (φ ∘ e)=e ⁻¹' tsupport φ := tsupport_comp_eq_preimage φ e.toHomeomorph
  rw [he]
  exact preimage_mono hf.2.2

private theorem rigid_forward_gradient {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Space n) :
    gradient (φ ∘ e.symm) (e x) = e.linearIsometryEquiv (gradient φ x) := by
  rw [gradient_comp_rigid e.symm hφ,e.symm_apply_apply]
  rfl

/-- Pullback of a raw Sobolev pair under an arbitrary rigid motion, on the
preimage of its domain. The supplied weak field transforms contravariantly. -/
theorem SobolevPair.comp_affine_isometry {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n→ℝ} {g : Space n→Space n} (hu : SobolevPair p D u g)
    (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    SobolevPair p (e ⁻¹' D) (u ∘ e) (fun x=>e.linearIsometryEquiv.symm (g (e x))) := by
  let E := e.linearIsometryEquiv
  have he := e.isometry.isClosedEmbedding.measurableEmbedding
  have hμ := (rigid_measurePreserving e).restrict_preimage_emb he D
  have hvg := hu.2.2.1.comp_measurePreserving hμ
  refine ⟨hu.1,hu.2.1.comp_measurePreserving hμ,hvg.of_le
    (E.symm.continuous.comp_aestronglyMeasurable hvg.1)
    (Eventually.of_forall (fun x=>(E.symm.norm_map (g (e x))).le)),?_⟩
  intro φ hφ i
  let ψ := φ ∘ e.symm
  have hD : e.symm ⁻¹' (e ⁻¹' D)=D := by ext x; simp
  have hψ : SmoothTest D ψ := hD ▸ rigid_test e.symm hφ
  let b := EuclideanSpace.basisFun (Fin n) ℝ i
  have hv := hu.2.2.2.directional_identity hψ (E b)
  let L := fun z=>u z*inner ℝ (gradient ψ z) (E b)
  let M := fun z=>inner ℝ (g z) (E b)*ψ z
  have heL : (fun x=>(u ∘ e) x*(gradient φ x) i)=L ∘ e := by
    funext x
    simp only [Function.comp_apply,L,ψ,rigid_forward_gradient e hφ.1,E,
      LinearIsometryEquiv.inner_map_map,b,EuclideanSpace.inner_basisFun_real]
  have heM : (fun x=>(E.symm (g (e x))) i*φ x)=M ∘ e := by
    funext x
    simp only [M,ψ,Function.comp_apply,e.symm_apply_apply]
    rw [←EuclideanSpace.inner_basisFun_real,E.symm.inner_map_eq_flip]
    rfl
  rw [heL,heM]
  exact ⟨(hμ.integrable_comp_emb he (g:=L)).mpr hv.1,(hμ.integrable_comp_emb he (g:=M)).mpr hv.2.1,
    (hμ.integral_comp he L).trans (hv.2.2.trans (congrArg Neg.neg (hμ.integral_comp he M).symm))⟩

/-- Euclidean rigid motions preserve the actual full local zero-boundary-test
weak p-harmonic equation for every p>1. -/
theorem WeakPHarmonicPair.comp_affine_isometry {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n→ℝ} {g : Space n→Space n} (hu : WeakPHarmonicPair p Ω u g)
    (e : Space n ≃ᵃⁱ[ℝ] Space n) :
    WeakPHarmonicPair p (e ⁻¹' Ω) (u ∘ e) (fun x=>e.linearIsometryEquiv.symm (g (e x))) := by
  let E := e.linearIsometryEquiv
  have hC {D : Set (Space n)} (hD : LocalDomain D (e ⁻¹' Ω)) : LocalDomain (e '' D) Ω := by
    refine ⟨e.toHomeomorph.isOpenMap _ hD.1,e.isometry.lipschitz.isBounded_image hD.2.1,?_⟩
    have hc : closure (e '' D) = e '' closure D := (e.toHomeomorph.image_closure D).symm
    rw [hc]
    exact image_subset_iff.mpr hD.2.2
  have hinv (D : Set (Space n)) : e ⁻¹' (e '' D)=D := preimage_image_eq _ e.injective
  apply weakPHarmonicPair_of_smooth_test_equation hu.1 (hu.2.1.preimage e.continuous)
  · intro D hD
    exact hinv D ▸ ((hu.2.2.1 _ (hC hD)).comp_affine_isometry e)
  · intro D hD φ hφ
    let ψ := φ ∘ e.symm
    have hψ : SmoothTest (e '' D) ψ := by
      have he : e.symm ⁻¹' D=e '' D := by
        ext z
        constructor
        · exact fun hz=>⟨e.symm z,hz,e.apply_symm_apply z⟩
        · rintro ⟨x,hx,rfl⟩
          change e.symm (e x) ∈ D
          rwa [e.symm_apply_apply]
      exact he ▸ rigid_test e.symm hφ
    have htest := (hu.2.2.2 _ (hC hD) ψ (gradient ψ) (hψ.zeroBoundarySobolevPair hu.1)).2
    have he (x : Space n) : fluxPairing p (fun y=>E.symm (g (e y))) (gradient φ) x =
        fluxPairing p g (gradient ψ) (e x) := by
      simp only [fluxPairing,ψ,rigid_forward_gradient e hφ.1,pFlux,LinearIsometryEquiv.norm_map,
        real_inner_smul_left]
      rw [E.symm.inner_map_eq_flip]
      rfl
    calc
      _ = ∫ x in D,fluxPairing p g (gradient ψ) (e x) := integral_congr_ae (Eventually.of_forall he)
      _ = ∫ z in e '' D,fluxPairing p g (gradient ψ) z := by
        have hI := (rigid_measurePreserving e).setIntegral_preimage_emb
          e.isometry.isClosedEmbedding.measurableEmbedding (fluxPairing p g (gradient ψ)) (e '' D)
        rwa [hinv D] at hI
      _ = 0 := htest

end BMCompactPDE
#print axioms BMCompactPDE.HasWeakGradientOn.directional_identity
#print axioms BMCompactPDE.SobolevPair.comp_affine_isometry
#print axioms BMCompactPDE.WeakPHarmonicPair.comp_affine_isometry
