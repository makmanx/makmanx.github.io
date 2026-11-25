import UpstreamFundamentalSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual polar integration and a raywise fundamental-theorem identity for
compactly supported smooth tests. These supply integration, not a postulated
distributional source law. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- Polar integration for an actual integrable scalar field,with the genuine
Euclidean polar sphere measure and its true radial Jacobian. -/
theorem integral_eq_sphere_ray {n : ℕ} (hn : 0<n)
    {f : Space n → ℝ} (hf : Integrable f volume) :
    (∫ x,f x) = ∫ θ : sphere (0 : Space n) 1,
      (∫ r in Ioi (0 : ℝ),r^(n-1)*f (r • (θ : Space n)))
        ∂(volume : Measure (Space n)).toSphere := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let μ : Measure (Space n) := volume
  let e := homeomorphUnitSphereProd (Space n)
  let F : sphere (0 : Space n) 1 × Ioi (0 : ℝ) → ℝ :=
    fun z => f ((e.symm z : ({0}ᶜ : Set (Space n))) : Space n)
  have hc : Integrable (f ∘ (↑) : ({0}ᶜ : Set (Space n)) → ℝ) (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hF : Integrable F (μ.toSphere.prod (Measure.volumeIoiPow (n-1))) := by
    have ht := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _) (g := F)).mp
      (by simpa only [F,e,Function.comp_def,Homeomorph.symm_apply_apply] using hc)
    simpa only [Space,finrank_euclideanSpace,Fintype.card_fin] using ht
  calc
    (∫ x,f x) = ∫ x : ({0}ᶜ : Set (Space n)),f (x : Space n) ∂μ.comap (↑) := by
      change (∫ x,f x ∂μ) = ∫ x : ({0}ᶜ : Set (Space n)),f (x : Space n) ∂μ.comap (↑)
      rw [integral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
    _ = ∫ z,F z ∂μ.toSphere.prod (Measure.volumeIoiPow (n-1)) := by
      have ht := hmp.integral_comp (Homeomorph.measurableEmbedding _) F
      simpa only [F,e,Function.comp_def,Homeomorph.symm_apply_apply,Space,
        finrank_euclideanSpace,Fintype.card_fin] using ht
    _ = ∫ θ : sphere (0 : Space n) 1,
        (∫ r : Ioi (0 : ℝ),f ((r : ℝ) • (θ : Space n)) ∂Measure.volumeIoiPow (n-1))
          ∂μ.toSphere := by
      rw [integral_prod F hF]
      rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with θ
      simp only [Measure.volumeIoiPow,ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const (n-1)).real_toNNReal)]
      rw [integral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => Real.toNNReal (r^(n-1)) • f (r • (θ : Space n)))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change Real.toNNReal (r^(n-1)) • f (r • (θ : Space n)) = r^(n-1)*f (r • (θ : Space n))
      rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hr.le _),smul_eq_mul]

/-- On every unit ray,the actual derivative of a compactly supported C1 test
integrates to minus its value at the pole. No source identity is assumed. -/
theorem integral_ray_gradient {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    {θ : Space n} (hθ : ‖θ‖=1) :
    (∫ r in Ioi (0 : ℝ),inner ℝ (gradient φ (r • θ)) θ) = -φ 0 := by
  let L : ℝ →ₗᵢ[ℝ] Space n :=
    { toLinearMap := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight θ
      norm_map' := by intro r;simp [norm_smul,hθ] }
  have hC : ContDiff ℝ 1 (fun r : ℝ => φ (r • θ)) :=
    hφ.comp L.toContinuousLinearMap.contDiff
  have hcompact : HasCompactSupport (fun r : ℝ => φ (r • θ)) :=
    hc.comp_isClosedEmbedding L.isometry.isClosedEmbedding
  have hd (r : ℝ) : deriv (fun t : ℝ => φ (t • θ)) r =
      inner ℝ (gradient φ (r • θ)) θ := by
    have ht := (hφ.differentiable one_ne_zero (r • θ)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const θ)
    have he : HasDerivAt (fun t : ℝ => φ (t • θ))
        (fderiv ℝ φ (r • θ) θ) r := by
      simpa only [Function.comp_def,id_eq,one_smul] using! ht
    rw [he.deriv,←toDual_gradient,toDual_apply_apply]
  have ht := HasCompactSupport.integral_Ioi_deriv_eq hC hcompact 0
  simpa only [hd,zero_smul] using ht

end BMCompactPDE
#print axioms BMCompactPDE.integral_eq_sphere_ray
#print axioms BMCompactPDE.integral_ray_gradient
