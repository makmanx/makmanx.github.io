import GradientUniformDifference
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Native local L2 weak-directional derivative extraction. The convolution pairing
limit is adapted from Lazyfill, accepted Prove2Me93835bcb-bdbc-4706-adbe-19b48ce839be.
The bounded-functional Riesz argument is adapted from sometik179's accepted
HunterInteriorH2 proof fcca92bd-0710-45e1-8717-932d87045928. Both retained private
proof bodies are credited dependencies; no new authorship is claimed for them.
They are not additional exported proof counts. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter BMCompactPDE
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace BMCompactGradientHessian
variable {n : ℕ}
section Pairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma hessian_translated_memLp {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (w : E) :
    MemLp (fun x => f (x - w)) 2 (volume : Measure E) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-w))
private lemma hessian_quotient_pairing_tendsto {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (v : E)
    {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto
      (fun t : ℝ => ∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x)
      (𝓝[≠] 0) (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => f (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  have hi : LocallyIntegrable (fun y => f (-y)) (volume : Measure E) :=
    (hf.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable
      (by norm_num)
  have hF (t : ℝ) : F t = ∫ x, f (x - t • v) * ψ x := by
    have h := integral_sub_left_eq_self
      (fun y => f (-y) * ψ (t • v - y)) (volume : Measure E) (t • v)
    simpa only [F, convolution_def, ContinuousLinearMap.mul_apply',
      neg_sub, sub_sub_cancel] using h.symm
  have hd : HasDerivAt F (∫ x, f x * fderiv ℝ ψ x v) 0 := by
    have h :=
      (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
        hi hψ (0 • v)).comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simp only [one_smul, zero_smul] at h
    apply h.congr_deriv
    calc
      _ = convolution (fun y => f (-y)) (fun x => fderiv ℝ ψ x v)
          (ContinuousLinearMap.mul ℝ ℝ) volume 0 :=
        convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
          (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) 0 v
      _ = ∫ x, f x * fderiv ℝ ψ x v := by
        simpa only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub] using
          integral_neg_eq_self (fun x => f x * fderiv ℝ ψ x v) volume
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have heq (t : ℝ) :
      (∫ x, (t⁻¹ * (f (x - t • v) - f x)) * ψ x) =
        t⁻¹ * (F t - F 0) := by
    have i₁ : Integrable (fun x => f (x - t • v) * ψ x)
        (volume : Measure E) :=
      (hessian_translated_memLp hf (t • v)).integrable_mul hp
    have i₀ : Integrable (fun x => f x * ψ x) (volume : Measure E) :=
      hf.integrable_mul hp
    rw [hF t, hF 0]
    simp only [zero_smul, sub_zero]
    calc
      _ = ∫ x, t⁻¹ * (f (x - t • v) * ψ x - f x * ψ x) := by
        apply integral_congr_ae
        exact .of_forall (fun x => by ring)
      _ = _ := by
        rw [integral_const_mul, integral_sub i₁ i₀]
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at ht
  exact ht.congr' (.of_forall fun t => (heq t).symm)

end Pairing

private theorem hessian_bounded_test_representation
    {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →ₗ[ℝ] H) (L : V →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, |L v| ≤ C * ‖J v‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ v, inner ℝ g (J v) = L v := by
  classical
  have heq : ∀ v w, J v = J w → L v = L w := by
    intro v w h
    have hb := hbound (v - w)
    have hz : J (v - w) = 0 := by rw [map_sub, h, sub_self]
    rw [hz, norm_zero, mul_zero, map_sub] at hb
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
  let pre : J.range → V := fun x => x.property.choose
  have hpre : ∀ x : J.range, J (pre x) = x := fun x => x.property.choose_spec
  let F : J.range →ₗ[ℝ] ℝ :=
    { toFun := fun x => L (pre x)
      map_add' := by
        intro x y
        rw [← map_add]
        apply heq
        rw [map_add, hpre, hpre, hpre]
        rfl
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply]
        rw [← map_smul]
        apply heq
        rw [map_smul, hpre, hpre]
        rfl }
  have hF : ∀ x : J.range, ‖F x‖ ≤ C * ‖x‖ := by
    intro x
    change |L (pre x)| ≤ C * ‖(x : H)‖
    simpa only [hpre] using hbound (pre x)
  let Fc : J.range →L[ℝ] ℝ := F.mkContinuous C hF
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq J.range Fc
  let g := (InnerProductSpace.toDual ℝ H).symm G
  refine ⟨g, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm G‖ ≤ C
    rw [LinearIsometryEquiv.norm_map, hnorm]
    exact Fc.opNorm_le_bound hC hF
  · intro v
    change inner ℝ ((InnerProductSpace.toDual ℝ H).symm G) (J v) = L v
    rw [InnerProductSpace.toDual_symm_apply]
    have hh := hG ⟨J v, ⟨v, rfl⟩⟩
    rw [hh]
    exact heq _ _ (hpre ⟨J v, ⟨v, rfl⟩⟩)


private def hessianTestSpace (Ω : Set (Space n)) : Submodule ℝ (Space n → ℝ) where
  carrier := {φ | SmoothTest Ω φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,
      (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨contDiff_const.smul hf.1,hf.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) f).trans hf.2.2⟩

private theorem hessianTest_memLp (Ω : Set (Space n)) (φ : hessianTestSpace Ω) :
    MemLp (φ : Space n → ℝ) 2 (volume.restrict Ω) :=
  (φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2.1).restrict _

private def hessianTestToLp (Ω : Set (Space n)) :
    hessianTestSpace Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun φ := (hessianTest_memLp Ω φ).toLp φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def hessianTestDeriv (Ω : Set (Space n)) (v : Space n) :
    hessianTestSpace Ω →ₗ[ℝ] (Space n → ℝ) where
  toFun φ := fun x => fderiv ℝ φ.val x v
  map_add' f g := by
    funext x
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [fderiv_add (f.property.1.differentiable (by simp)).differentiableAt
      (g.property.1.differentiable (by simp)).differentiableAt]
    rfl
  map_smul' c f := by
    funext x
    simp only [Submodule.coe_smul,Pi.smul_apply,RingHom.id_apply]
    rw [fderiv_const_smul (f.property.1.differentiable (by simp)).differentiableAt]
    rfl

private theorem hessianTestDeriv_isTest (Ω : Set (Space n)) (v : Space n)
    (φ : hessianTestSpace Ω) : SmoothTest Ω (hessianTestDeriv Ω v φ) := by
  refine ⟨?_,φ.property.2.1.fderiv_apply ℝ _,?_⟩
  · exact (φ.property.1.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (tsupport_fderiv_apply_subset ℝ _).trans φ.property.2.2

private theorem hessianTestDeriv_memLp (Ω : Set (Space n)) (v : Space n)
    (φ : hessianTestSpace Ω) : MemLp (hessianTestDeriv Ω v φ) 2 (volume.restrict Ω) :=
  ((hessianTestDeriv_isTest Ω v φ).1.continuous.memLp_of_hasCompactSupport
    (hessianTestDeriv_isTest Ω v φ).2.1).restrict _

private def hessianDerivativeFunctional {Ω : Set (Space n)} (f : Space n → ℝ)
    (hf : MemLp f 2 (volume.restrict Ω)) (v : Space n) : hessianTestSpace Ω →ₗ[ℝ] ℝ where
  toFun φ := -∫ x in Ω,f x*hessianTestDeriv Ω v φ x
  map_add' φ ψ := by
    simp only [map_add,Pi.add_apply,mul_add]
    have hφ : Integrable (fun x => f x*hessianTestDeriv Ω v φ x) (volume.restrict Ω) :=
      hf.integrable_mul (hessianTestDeriv_memLp Ω v φ)
    have hψ : Integrable (fun x => f x*hessianTestDeriv Ω v ψ x) (volume.restrict Ω) :=
      hf.integrable_mul (hessianTestDeriv_memLp Ω v ψ)
    rw [integral_add hφ hψ]
    ring
  map_smul' c φ := by
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm (f _) c]
    rw [integral_const_mul]
    ring

private theorem hessian_distributional_representative
    {Ω : Set (Space n)} (f : Space n → ℝ) (hf : MemLp f 2 (volume.restrict Ω))
    (v : Space n) (C : ℝ) (hC : 0≤C)
    (hbound : ∀ φ : hessianTestSpace Ω,
      |∫ x in Ω,f x*hessianTestDeriv Ω v φ x|≤C*‖hessianTestToLp Ω φ‖) :
    ∃ g : Space n → ℝ,MemLp g 2 (volume.restrict Ω) ∧
      (eLpNorm g 2 (volume.restrict Ω)).toReal≤C ∧
      ∀ φ : hessianTestSpace Ω,∫ x in Ω,g x*φ.val x=
        -∫ x in Ω,f x*hessianTestDeriv Ω v φ x := by
  obtain ⟨g,hg,hrepr⟩ := hessian_bounded_test_representation (hessianTestToLp Ω)
    (hessianDerivativeFunctional f hf v) C hC (fun φ => by
      simpa only [hessianDerivativeFunctional,LinearMap.coe_mk,AddHom.coe_mk,abs_neg]
        using hbound φ)
  refine ⟨g,Lp.memLp g,?_,?_⟩
  · simpa only [←Lp.norm_def] using hg
  · intro φ
    have hh := hrepr φ
    rw [L2.inner_def] at hh
    change (∫ x in Ω,(hessianTestToLp Ω φ) x*g x)=_ at hh
    change _=hessianDerivativeFunctional f hf v φ
    rw [←hh]
    apply integral_congr_ae
    filter_upwards [(hessianTest_memLp Ω φ).coeFn_toLp] with x hx
    change (hessianTestToLp Ω φ) x=φ.val x at hx
    rw [hx,mul_comm]

private theorem hessian_abs_pairing_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x,f x*g x ∂μ|≤(eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal := by
  have he : (∫ x,f x*g x ∂μ)=inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
    simp only [RCLike.inner_apply,hfx,hgx,starRingEnd_apply,star_trivial]
    ring
  rw [he]
  simpa only [Real.norm_eq_abs,Lp.norm_toLp] using
    norm_inner_le_norm (𝕜:=ℝ) (hf.toLp f) (hg.toLp g)

/-- An actual local L2 quotient bound constructs an actual local weak derivative.
The domain may be arbitrary; the global L2 input is the canonical zero extension
used later for actual PDE gradient components. No derivative is an input. -/
theorem exists_l2_directional_derivative_of_local_quotient_bound
    {Ω : Set (Space n)} {f : Space n → ℝ} (hf : MemLp f 2 volume)
    (v : Space n) (C : ℝ) (hC : 0≤C)
    (hquot : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      MemLp (fun x => t⁻¹*(f (x-t • v)-f x)) 2 (volume.restrict Ω) ∧
      (eLpNorm (fun x => t⁻¹*(f (x-t • v)-f x)) 2 (volume.restrict Ω)).toReal≤C) :
    ∃ g : Space n → ℝ,MemLp g 2 (volume.restrict Ω) ∧
      (eLpNorm g 2 (volume.restrict Ω)).toReal≤C ∧
      ∀ φ : Space n → ℝ,SmoothTest Ω φ →
        Integrable (fun x => f x*fderiv ℝ φ x v) (volume.restrict Ω) ∧
        Integrable (fun x => g x*φ x) (volume.restrict Ω) ∧
        (∫ x in Ω,f x*fderiv ℝ φ x v)=-(∫ x in Ω,g x*φ x) := by
  have hfΩ := hf.restrict Ω
  have hbound : ∀ φ : hessianTestSpace Ω,
      |∫ x in Ω,f x*hessianTestDeriv Ω v φ x|≤C*‖hessianTestToLp Ω φ‖ := by
    intro φ
    have ht := (hessian_quotient_pairing_tendsto hf v
      (φ.property.1.of_le (by simp)) φ.property.2.1).abs
    have hderiv : (∫ x in Ω,f x*hessianTestDeriv Ω v φ x)=
        ∫ x,f x*fderiv ℝ φ.val x v := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : hessianTestDeriv Ω v φ x=0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx ((hessianTestDeriv_isTest Ω v φ).2.2 hh))
      change f x*hessianTestDeriv Ω v φ x=0
      rw [hz,mul_zero]
    rw [hderiv]
    have hlim : |∫ x,f x*fderiv ℝ φ.val x v|≤C*‖hessianTestToLp Ω φ‖ := by
      apply le_of_tendsto ht
      filter_upwards [hquot] with t hqt
      have he : (∫ x in Ω,(t⁻¹*(f (x-t • v)-f x))*φ.val x)=
          ∫ x,(t⁻¹*(f (x-t • v)-f x))*φ.val x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (φ.property.2.2 hh)),mul_zero]
      rw [←he]
      have hb := (hessian_abs_pairing_le hqt.1 (hessianTest_memLp Ω φ)).trans
        (mul_le_mul_of_nonneg_right hqt.2 ENNReal.toReal_nonneg)
      change _≤C*‖(hessianTest_memLp Ω φ).toLp φ.val‖
      rw [Lp.norm_toLp]
      exact hb
    exact hlim
  obtain ⟨g,hg,hgN,hgtest⟩ := hessian_distributional_representative f hfΩ v C hC hbound
  refine ⟨g,hg,hgN,?_⟩
  intro φ hφ
  let ψ : hessianTestSpace Ω := ⟨φ,hφ⟩
  refine ⟨hfΩ.integrable_mul (hessianTestDeriv_memLp Ω v ψ),
    hg.integrable_mul (hessianTest_memLp Ω ψ),?_⟩
  have h := hgtest ψ
  change (∫ x in Ω,g x*φ x)=-(∫ x in Ω,f x*fderiv ℝ φ x v) at h
  linarith

#print axioms exists_l2_directional_derivative_of_local_quotient_bound

end BMCompactGradientHessian
