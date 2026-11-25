import AlexandrovConvex
import SupInfConv
import SuperDivergence
import TouchingPLaplace

/-! Bridge from second-order Taylor expansions (`HasSecondOrderTaylorAt`) to
viscosity p-subsolution and positive-source supersolution inequalities, plus
monotonicity and operator-norm bounds for symmetric Hessians. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff BigOperators
namespace BMCompactPDE

section MatrixPLaplace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Matrix form of the normalized p-Laplacian at gradient `g` and Hessian `A`. -/
def matrixNormalizedPLaplacian (p : ℝ) (g : E) (A : E →L[ℝ] E) : ℝ :=
  LinearMap.trace ℝ E A.toLinearMap +
    (p - 2) * (‖g‖ ^ 2)⁻¹ * inner ℝ (A g) g

/-- Quadratic Taylor model centered at `x`. -/
def quadModel (c : ℝ) (g : E) (A : E →L[ℝ] E) (x y : E) : ℝ :=
  c + inner ℝ g (y - x) + (1 / 2 : ℝ) * inner ℝ (A (y - x)) (y - x)

theorem contDiff_quadModel (c : ℝ) (g : E) (A : E →L[ℝ] E) (x : E) :
    ContDiff ℝ ∞ (quadModel c g A x) := by
  unfold quadModel
  have hsub : ContDiff ℝ ∞ (fun y : E => y - x) := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (contDiff_const.inner ℝ hsub)).add
    (contDiff_const.mul ((A.contDiff.comp hsub).inner ℝ hsub))

theorem hasFDerivAt_quadModel (c : ℝ) (g : E) {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (x y : E) :
    HasFDerivAt (quadModel c g A x)
      (toDual ℝ E (g + A (y - x))) y := by
  unfold quadModel
  have hsub : HasFDerivAt (fun z : E => z - x) (ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).sub_const x
  have h1 : HasFDerivAt (fun z : E => c + inner ℝ g (z - x)) (toDual ℝ E g) y := by
    have hlin : HasFDerivAt (fun z : E => inner ℝ g (z - x)) (toDual ℝ E g) y := by
      have h := (hasFDerivAt_const g y).inner ℝ hsub
      refine h.congr_fderiv ?_
      ext v; simp [toDual_apply_apply]
    have hadd := (hasFDerivAt_const c y).add hlin
    refine hadd.congr_fderiv ?_
    ext v; simp
  have h2 : HasFDerivAt (fun z : E => inner ℝ (A (z - x)) (z - x))
      ((2 : ℝ) • toDual ℝ E (A (y - x))) y := by
    have hA : HasFDerivAt (fun z : E => A (z - x)) A y := by
      have h := A.hasFDerivAt.comp y hsub
      exact h.congr_fderiv (ContinuousLinearMap.comp_id A)
    have hprod := hA.inner ℝ hsub
    refine hprod.congr_fderiv ?_
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, fderivInnerCLM_apply, toDual_apply_apply, smul_eq_mul]
    have hcomm : inner ℝ (A v) (y - x) = inner ℝ (A (y - x)) v := by
      rw [hsymm v (y - x), real_inner_comm]
    linarith
  have h3 := h1.add (h2.const_mul (1 / 2 : ℝ))
  refine h3.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    toDual_apply_apply, inner_add_left, smul_eq_mul]
  ring

theorem gradient_quadModel (c : ℝ) (g : E) {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (x y : E) :
    gradient (quadModel c g A x) y = g + A (y - x) := by
  have h := hasFDerivAt_quadModel c g hsymm x y
  simpa [LinearIsometryEquiv.symm_apply_apply] using h.hasGradientAt.gradient

theorem gradient_quadModel_self (c : ℝ) (g : E) {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (x : E) :
    gradient (quadModel c g A x) x = g := by
  rw [gradient_quadModel c g hsymm x x, sub_self, map_zero, add_zero]

theorem actualHessian_quadModel (c : ℝ) (g : E) {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (x : E) (u v : E) :
    BMCompactAnalytic.actualHessian (quadModel c g A x) x u v = inner ℝ (A u) v := by
  have hfderiv : fderiv ℝ (quadModel c g A x) =
      fun y => toDual ℝ E (g + A (y - x)) := by
    funext y; exact (hasFDerivAt_quadModel c g hsymm x y).fderiv
  have h2 : HasFDerivAt (fderiv ℝ (quadModel c g A x))
      ((toDual ℝ E).toContinuousLinearMap.comp A) x := by
    rw [hfderiv]
    have hsub : HasFDerivAt (fun y : E => g + A (y - x)) A x := by
      have h1 : HasFDerivAt (fun y : E => A (y - x)) A x :=
        (A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)).congr_fderiv
          (ContinuousLinearMap.comp_id A)
      exact ((hasFDerivAt_const g x).add h1).congr_fderiv (zero_add A)
    exact (toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x hsub
  unfold BMCompactAnalytic.actualHessian
  rw [h2.fderiv]
  simp [toDual_apply_apply]

theorem normalizedPLaplacian_quadModel (p c : ℝ) (g : E) {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (x : E) :
    BMCompactAnalytic.normalizedPLaplacian p (quadModel c g A x) x =
      matrixNormalizedPLaplacian p g A := by
  unfold BMCompactAnalytic.normalizedPLaplacian matrixNormalizedPLaplacian
    BMCompactAnalytic.actualLaplacian BMCompactAnalytic.actualHessianEnd
  rw [gradient_quadModel_self c g hsymm x, actualHessian_quadModel c g hsymm x g g]
  congr 2
  ext u
  change (toDual ℝ E).symm (BMCompactAnalytic.actualHessian (quadModel c g A x) x u) = A u
  apply (toDual ℝ E).injective
  rw [(toDual ℝ E).apply_symm_apply]
  ext v
  rw [toDual_apply_apply, actualHessian_quadModel c g hsymm x u v]

theorem matrixNormalizedPLaplacian_mono {p : ℝ} (hp : 1 < p) {g : E} (hg : g ≠ 0)
    {A B : E →L[ℝ] E} (hle : ∀ v : E, inner ℝ (A v) v ≤ inner ℝ (B v) v) :
    matrixNormalizedPLaplacian p g A ≤ matrixNormalizedPLaplacian p g B := by
  classical
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let ν : E := ‖g‖⁻¹ • g
  have hν : ‖ν‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hgpos.le), inv_mul_cancel₀ hgpos.ne']
  obtain ⟨s, basis, i₀, hi₀⟩ := BMCompactAnalytic.exists_orthonormalBasis_containing hν
  have htr (T : E →L[ℝ] E) : LinearMap.trace ℝ E T.toLinearMap =
      ∑ i : s, inner ℝ (T (basis i)) (basis i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ basis.toBasis]
    change (∑ i : s, (LinearMap.toMatrix basis.toBasis basis.toBasis T.toLinearMap) i i) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply, basis.coe_toBasis, basis.coe_toBasis_repr_apply,
      basis.repr_apply_apply, real_inner_comm]
    rfl
  have hrew (T : E →L[ℝ] E) : matrixNormalizedPLaplacian p g T =
      ∑ i : s, (if i = i₀ then p - 1 else 1) * inner ℝ (T (basis i)) (basis i) := by
    rw [BMCompactAnalytic.elliptic_weighted_sum i₀ p (fun i => inner ℝ (T (basis i)) (basis i)),
      ← htr T, hi₀]
    unfold matrixNormalizedPLaplacian
    dsimp only [ν]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    congr 1
    field_simp [hgpos.ne']
  rw [hrew A, hrew B]
  apply Finset.sum_le_sum
  intro i _
  have hw : 0 ≤ (if i = i₀ then p - 1 else 1) := by split_ifs <;> linarith
  exact mul_le_mul_of_nonneg_left (hle (basis i)) hw

theorem matrixNormalizedPLaplacian_add (p : ℝ) (g : E) (A B : E →L[ℝ] E) :
    matrixNormalizedPLaplacian p g (A + B) =
      matrixNormalizedPLaplacian p g A + matrixNormalizedPLaplacian p g B := by
  unfold matrixNormalizedPLaplacian
  rw [ContinuousLinearMap.coe_add, map_add, ContinuousLinearMap.add_apply, inner_add_left]
  ring

theorem matrixNormalizedPLaplacian_smul (p c : ℝ) (g : E) (A : E →L[ℝ] E) :
    matrixNormalizedPLaplacian p g (c • A) = c * matrixNormalizedPLaplacian p g A := by
  unfold matrixNormalizedPLaplacian
  rw [ContinuousLinearMap.coe_smul, map_smul, ContinuousLinearMap.smul_apply,
    real_inner_smul_left, smul_eq_mul]
  ring

/-- Operator norm bound for a symmetric linear map from its quadratic form. -/
theorem opNorm_le_of_symmetric_quad_bound {A : E →L[ℝ] E}
    (hsymm : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {K : ℝ} (hK : 0 ≤ K) (hquad : ∀ v : E, |inner ℝ (A v) v| ≤ K * ‖v‖ ^ 2) :
    ‖A‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound A hK fun u => ?_
  by_cases hu : u = 0
  · simp [hu]
  by_cases hAu : A u = 0
  · rw [hAu, norm_zero]; positivity
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hAu_pos : 0 < ‖A u‖ := norm_pos_iff.mpr hAu
  let u' : E := ‖u‖⁻¹ • u
  let v' : E := ‖A u‖⁻¹ • A u
  have hu'_norm : ‖u'‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hu_pos.le), inv_mul_cancel₀ hu_pos.ne']
  have hv'_norm : ‖v'‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hAu_pos.le), inv_mul_cancel₀ hAu_pos.ne']
  have hpol : 4 * inner ℝ (A u') v' =
      inner ℝ (A (u' + v')) (u' + v') - inner ℝ (A (u' - v')) (u' - v') := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [hsymm v' u', real_inner_comm v' (A u')]
    ring
  have hpar : ‖u' + v'‖ ^ 2 + ‖u' - v'‖ ^ 2 = 2 * (‖u'‖ ^ 2 + ‖v'‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have h1 := (abs_le.mp (hquad (u' + v'))).2
  have h2 := (abs_le.mp (hquad (u' - v'))).1
  have hle4 : 4 * inner ℝ (A u') v' ≤ 4 * K := by
    rw [hpol]
    have : K * ‖u' + v'‖ ^ 2 + K * ‖u' - v'‖ ^ 2 = 4 * K := by
      rw [← mul_add, hpar, hu'_norm, hv'_norm]; ring
    linarith
  have hinner_eq : inner ℝ (A u') v' = ‖A u‖ / ‖u‖ := by
    dsimp only [u', v']
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hu_pos.ne', hAu_pos.ne']
  rw [hinner_eq] at hle4
  have hdiv : ‖A u‖ / ‖u‖ ≤ K := by linarith
  exact (div_le_iff₀ hu_pos).mp hdiv

/-- Convexity + second-order Taylor expansion implies positive semidefinite Hessian. -/
theorem HasSecondOrderTaylorAt.psd_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {g : E} {A : E →L[ℝ] E} {x : E} (ht : HasSecondOrderTaylorAt f g A x)
    (hsub : IsSubgradient f x g) (v : E) : 0 ≤ inner ℝ (A v) v := by
  by_contra hneg
  push_neg at hneg
  have hv0 : v ≠ 0 := by
    intro hv; subst hv; simp at hneg
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hneg' : 0 < -inner ℝ (A v) v := neg_pos.mpr hneg
  let ε : ℝ := -inner ℝ (A v) v / (4 * ‖v‖ ^ 2)
  have hε : 0 < ε := by positivity
  have hlo := ht.2
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hr_bound⟩ := Metric.eventually_nhds_iff.mp (hlo hε)
  let t : ℝ := r / (2 * ‖v‖)
  have ht_pos : 0 < t := by positivity
  have hdist : dist (x + t • v) x < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht_pos.le]
    dsimp only [t]; field_simp [hv_pos.ne']; linarith
  have hb := hr_bound hdist
  rw [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _),
    map_smul, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
    norm_smul, Real.norm_of_nonneg ht_pos.le] at hb
  have hge := hsub (x + t • v)
  rw [add_sub_cancel_left, real_inner_smul_right] at hge
  have hupper := (abs_le.mp hb).2
  have hεeq : ε * (t * ‖v‖) ^ 2 = -(1 / 4 : ℝ) * t ^ 2 * inner ℝ (A v) v := by
    dsimp only [ε]; field_simp [hv_pos.ne']
  have hcomb : (1 / 4 : ℝ) * t ^ 2 * inner ℝ (A v) v ≥ 0 := by
    have : -(1 / 2 : ℝ) * (t * (t * inner ℝ (A v) v)) ≤ ε * (t * ‖v‖) ^ 2 := by linarith
    rw [hεeq] at this; nlinarith
  have hneg2 : (1 / 4 : ℝ) * t ^ 2 * inner ℝ (A v) v < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

/-- Subtracting `(M / 2) * ‖y‖ ^ 2` shifts the second-order Taylor expansion. -/
theorem HasSecondOrderTaylorAt.sub_quad {f : E → ℝ} {g : E} {A : E →L[ℝ] E} {x : E}
    (ht : HasSecondOrderTaylorAt f g A x) (M : ℝ) :
    HasSecondOrderTaylorAt (fun y => f y - (M / 2) * ‖y‖ ^ 2)
      (g - M • x) (A - M • ContinuousLinearMap.id ℝ E) x := by
  refine ⟨fun u v => ?_, ?_⟩
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, ht.1 u v]
  · refine ht.2.congr' (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun _ => rfl)
    have hnorm : ‖y‖ ^ 2 - ‖x‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * inner ℝ x (y - x) := by
      have hvec : y = (y - x) + x := by abel
      conv_lhs => rw [hvec, norm_add_sq_real]
      rw [real_inner_comm (y - x) x]; ring
    have hself : inner ℝ (y - x) (y - x) = ‖y - x‖ ^ 2 := real_inner_self_eq_norm_sq (y - x)
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, real_inner_smul_left]
    have hself' : inner ℝ y (y - x) - inner ℝ x (y - x) = ‖y - x‖ ^ 2 := by
      rw [← inner_sub_left, hself]
    rw [hself']
    have hny : ‖y‖ ^ 2 = ‖x‖ ^ 2 + ‖y - x‖ ^ 2 + 2 * inner ℝ x (y - x) := by linarith [hnorm]
    rw [hny]
    ring

/-- Negating a function negates its second-order Taylor expansion. -/
theorem HasSecondOrderTaylorAt.neg {f : E → ℝ} {g : E} {A : E →L[ℝ] E} {x : E}
    (ht : HasSecondOrderTaylorAt f g A x) :
    HasSecondOrderTaylorAt (fun y => -f y) (-g) (-A) x := by
  refine ⟨fun u v => ?_, ?_⟩
  · simp only [ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right, ht.1 u v]
  · refine ht.2.neg_left.congr' (Eventually.of_forall fun y => ?_) (Eventually.of_forall fun _ => rfl)
    simp only [ContinuousLinearMap.neg_apply, inner_neg_left]
    ring

/-- At a second-order Taylor point with nonzero gradient, a viscosity
p-subsolution satisfies `0 ≤ matrixNormalizedPLaplacian p g A`. -/
theorem HasSecondOrderTaylorAt.matrixNormalizedPLaplacian_nonneg
    {p : ℝ} {Ω : Set E} {u : E → ℝ}
    (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u)
    {x : E} (hx : x ∈ Ω) {g : E} {A : E →L[ℝ] E}
    (ht : HasSecondOrderTaylorAt u g A x) (hg : g ≠ 0) :
    0 ≤ matrixNormalizedPLaplacian p g A := by
  have hfor (δ : ℝ) (hδ : 0 < δ) :
      0 ≤ matrixNormalizedPLaplacian p g (A + δ • ContinuousLinearMap.id ℝ E) := by
    let B : E →L[ℝ] E := A + δ • ContinuousLinearMap.id ℝ E
    have hBsymm : ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := fun u v => by
      simp only [B, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, ht.1 u v]
    let φ : E → ℝ := quadModel (u x) g B x
    have hφ2 : ContDiffAt ℝ 2 φ x :=
      ((contDiff_quadModel (u x) g B x).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hφx : u x = φ x := by simp [φ, quadModel]
    have hφg : gradient φ x ≠ 0 := by
      rw [gradient_quadModel_self (u x) g hBsymm x]; exact hg
    have hupper : ∀ᶠ y in 𝓝 x, u y ≤ φ y := by
      have hlo := ht.2
      rw [Asymptotics.isLittleO_iff] at hlo
      filter_upwards [hlo (half_pos hδ)] with y hy
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)] at hy
      have h1 := (abs_le.mp hy).2
      dsimp only [φ, quadModel, B]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      linarith
    have hres := hu.2.2.2 x hx φ hφ2 hφx hupper hφg
    rwa [normalizedPLaplacian_quadModel p (u x) g hBsymm x] at hres
  have hlim : Tendsto (fun δ : ℝ =>
      matrixNormalizedPLaplacian p g A + δ * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ E))
      (𝓝[>] 0) (𝓝 (matrixNormalizedPLaplacian p g A)) := by
    have h1 : Tendsto (fun δ : ℝ =>
        matrixNormalizedPLaplacian p g A + δ * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ E))
        (𝓝 0) (𝓝 (matrixNormalizedPLaplacian p g A + 0 * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ E))) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    simpa using h1.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  rw [← matrixNormalizedPLaplacian_smul, ← matrixNormalizedPLaplacian_add]
  exact hfor δ hδ

end MatrixPLaplace

section SpaceN
variable {n : ℕ}

/-- At a second-order Taylor point with nonzero gradient, a function satisfying
the strict lower-contact divergence bound with source `c` obeys
`‖g‖^(p-2) * matrixNormalizedPLaplacian p g A ≤ -c`. -/
theorem HasSecondOrderTaylorAt.matrixClassicalPLaplacian_le_neg_source
    {p c : ℝ} {D : Set (Space n)} (hD : IsOpen D)
    {v : Space n → ℝ} {x : Space n} (hx : x ∈ D)
    {g : Space n} {A : Space n →L[ℝ] Space n}
    (ht : HasSecondOrderTaylorAt v g A x) (hg : g ≠ 0)
    (hcontact : ∀ (U : Set (Space n)), IsOpen U → U ⊆ D → x ∈ U →
      ∀ (φ : Space n → ℝ), ContDiffOn ℝ 1 φ U →
        ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) U →
        v x = φ x → (∀ y ∈ U, y ≠ x → φ y < v y) →
        c ≤ -coordinateDivergence (fun y => pFlux p (gradient φ y)) x) :
    ‖g‖ ^ (p - 2) * matrixNormalizedPLaplacian p g A ≤ -c := by
  have hfor (δ : ℝ) (hδ : 0 < δ) :
      c ≤ -(‖g‖ ^ (p - 2) * matrixNormalizedPLaplacian p g (A + (-δ) • ContinuousLinearMap.id ℝ (Space n))) := by
    let B : Space n →L[ℝ] Space n := A + (-δ) • ContinuousLinearMap.id ℝ (Space n)
    have hBsymm : ∀ u w, inner ℝ (B u) w = inner ℝ u (B w) := fun u w => by
      simp only [B, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, ht.1 u w]
    let φ : Space n → ℝ := quadModel (v x) g B x
    have hφ_smooth : ContDiff ℝ ∞ φ := contDiff_quadModel (v x) g B x
    have hφx : v x = φ x := by simp [φ, quadModel]
    have hgrad_cont : Continuous (gradient φ) := by
      have heq : gradient φ = fun y => g + B (y - x) := funext (gradient_quadModel (v x) g hBsymm x)
      rw [heq]; exact continuous_const.add (B.continuous.comp (continuous_id.sub continuous_const))
    have hlo := ht.2
    rw [Asymptotics.isLittleO_iff] at hlo
    obtain ⟨r₁, hr₁, hr₁_bound⟩ :=
      Metric.eventually_nhds_iff.mp (hlo (show (0 : ℝ) < δ / 4 by positivity))
    have hopen_ne : IsOpen {y : Space n | gradient φ y ≠ 0} :=
      isOpen_ne.preimage hgrad_cont
    have hx_ne : gradient φ x ≠ 0 := by
      rw [gradient_quadModel_self (v x) g hBsymm x]; exact hg
    let U : Set (Space n) := D ∩ ball x r₁ ∩ {y | gradient φ y ≠ 0}
    have hUopen : IsOpen U := (hD.inter isOpen_ball).inter hopen_ne
    have hxU : x ∈ U := ⟨⟨hx, mem_ball_self hr₁⟩, hx_ne⟩
    have hUD : U ⊆ D := inter_subset_left.trans inter_subset_left
    have hφ1 : ContDiffOn ℝ 1 φ U := (hφ_smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
    have hF1 : ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) U :=
      contDiffOn_pFlux_gradient_of_contDiffOn_two p hUopen
        ((hφ_smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) (fun _ hy => hy.2)
    have hstrict : ∀ y ∈ U, y ≠ x → φ y < v y := by
      intro y hyU hyne
      have hb := hr₁_bound hyU.1.2
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)] at hb
      have h1 := (abs_le.mp hb).1
      have hpos_sq : 0 < ‖y - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyne))
      dsimp only [φ, quadModel, B]
      simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith
    have hres := hcontact U hUopen hUD hxU φ hφ1 hF1 hφx hstrict
    have hdiv_eq : coordinateDivergence (fun y => pFlux p (gradient φ y)) x =
        ‖g‖ ^ (p - 2) * matrixNormalizedPLaplacian p g B := by
      have hFd : DifferentiableAt ℝ (fun y => pFlux p (gradient φ y)) x :=
        (hF1.contDiffAt (hUopen.mem_nhds hxU)).differentiableAt (by norm_num)
      unfold coordinateDivergence
      rw [← classicalDivergence_eq_sum_gradient_coordinates hFd,
        classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
          ((hφ_smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) hx_ne]
      unfold BMCompactAnalytic.classicalPLaplacian
      rw [gradient_quadModel_self (v x) g hBsymm x, normalizedPLaplacian_quadModel p (v x) g hBsymm x]
    rwa [hdiv_eq] at hres
  have hlim : Tendsto (fun δ : ℝ =>
      -(‖g‖ ^ (p - 2) * (matrixNormalizedPLaplacian p g A +
        (-δ) * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ (Space n)))))
      (𝓝[>] 0) (𝓝 (-(‖g‖ ^ (p - 2) * matrixNormalizedPLaplacian p g A))) := by
    have h1 : Tendsto (fun δ : ℝ =>
        -(‖g‖ ^ (p - 2) * (matrixNormalizedPLaplacian p g A +
          (-δ) * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ (Space n)))))
        (𝓝 0) (𝓝 (-(‖g‖ ^ (p - 2) * (matrixNormalizedPLaplacian p g A +
          (-0) * matrixNormalizedPLaplacian p g (ContinuousLinearMap.id ℝ (Space n)))))) :=
      ((tendsto_const_nhds.add (tendsto_id.neg.mul tendsto_const_nhds)).const_mul _).neg
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hge := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [← matrixNormalizedPLaplacian_smul, ← matrixNormalizedPLaplacian_add]
    exact hfor δ hδ)
  linarith

end SpaceN
end BMCompactPDE
#print axioms BMCompactPDE.matrixNormalizedPLaplacian_mono
#print axioms BMCompactPDE.opNorm_le_of_symmetric_quad_bound
#print axioms BMCompactPDE.HasSecondOrderTaylorAt.matrixNormalizedPLaplacian_nonneg
#print axioms BMCompactPDE.HasSecondOrderTaylorAt.matrixClassicalPLaplacian_le_neg_source
