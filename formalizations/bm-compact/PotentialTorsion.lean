import RootDoublingComparison

/-! Concrete positive-source profiles for every p>1, with a genuine critical
point. Their actual nonlinear gradient flux is globally affine, even when the
profile is not C2 at its centre. No weak PDE or regularity premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

def potentialTorsion {n : ℕ} (p c C : ℝ) (a x : Space n) : ℝ :=
  flatContactPower (p/(p-1)) ((c/(n : ℝ))^((p-1)⁻¹)) C a x

private theorem potential_torsion_exponent {p : ℝ} (hp : 1<p) :
    1<p/(p-1) ∧ (p/(p-1)-1)*(p-1)-1=0 := by
  have hd : 0<p-1 := sub_pos.mpr hp
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · field_simp [hd.ne']
    <;> ring

/-- Exact global affine flux of the actual power profile, including its
zero-gradient centre and the singular exponent range 1<p<2. -/
theorem pFlux_gradient_potentialTorsion {n : ℕ} {p c : ℝ}
    (hp : 1<p) (hc : 0<c) (hn : 2≤n) (C : ℝ) (a x : Space n) :
    pFlux p (gradient (potentialTorsion p c C a) x)=
      (-(c/(n : ℝ))) • (x-a) := by
  have hn0 : 0<(n : ℝ) := by exact_mod_cast (by omega : 0<n)
  have hd : 0<p-1 := sub_pos.mpr hp
  have hBase : 0<c/(n : ℝ) := div_pos hc hn0
  let A : ℝ := (c/(n : ℝ))^((p-1)⁻¹)
  have hA : 0<A := Real.rpow_pos_of_pos hBase _
  have hAP : A^(p-1)=c/(n : ℝ) := by
    dsimp only [A]
    rw [←Real.rpow_mul hBase.le,inv_mul_cancel₀ hd.ne',Real.rpow_one]
  have he : A^(p-2)*A=A^(p-1) := by
    calc
      A^(p-2)*A=A^(p-2)*A^1 := by rw [Real.rpow_one]
      _=A^((p-2)+1) := (Real.rpow_add hA _ _).symm
      _=A^(p-1) := by congr 1 <;> ring
  have hcoef : |-A|^(p-2)*(-A)=-(c/(n : ℝ)) := by
    rw [abs_neg,abs_of_pos hA,mul_neg,he,hAP]
  unfold potentialTorsion
  rw [pFlux_gradient_flatContactPower hp (potential_torsion_exponent hp).1,
    (potential_torsion_exponent hp).2,Real.rpow_zero,one_smul]
  exact congrArg (fun r : ℝ => r • (x-a)) hcoef

/-- The ACTUAL divergence is -c everywhere; the critical point is included. -/
theorem coordinateDivergence_flux_potentialTorsion {n : ℕ} {p c : ℝ}
    (hp : 1<p) (hc : 0<c) (hn : 2≤n) (C : ℝ) (a x : Space n) :
    coordinateDivergence (fun y => pFlux p (gradient (potentialTorsion p c C a) y)) x = -c := by
  have he : (fun y => pFlux p (gradient (potentialTorsion p c C a) y)) =
      fun y => (-(c/(n : ℝ))) • (y-a) := funext (pFlux_gradient_potentialTorsion hp hc hn C a)
  rw [he]
  have hd : HasFDerivAt (fun y : Space n => (-(c/(n : ℝ))) • (y-a))
      ((-(c/(n : ℝ))) • ContinuousLinearMap.id ℝ (Space n)) x := by
    have hi : HasFDerivAt (fun y : Space n => y-a)
        (ContinuousLinearMap.id ℝ (Space n)) x := (hasFDerivAt_id x).sub_const a
    exact hi.const_smul (-(c/(n : ℝ)))
  unfold coordinateDivergence
  rw [←classicalDivergence_eq_sum_gradient_coordinates hd.differentiableAt]
  unfold classicalDivergence
  rw [hd.fderiv]
  change LinearMap.trace ℝ (Space n)
    ((-(c/(n : ℝ))) • LinearMap.id) = -c
  rw [map_smul,LinearMap.trace_id]
  simp only [Space,finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul]
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  field_simp

/-- The concrete profile satisfies the full actual W0 weak source equation
on every open domain, with its actual classical gradient as the weak field. -/
theorem weakPSourcePair_potentialTorsion {n : ℕ} {p c : ℝ}
    (hp : 1<p) (hc : 0<c) (hn : 2≤n) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    (C : ℝ) (a : Space n) :
    WeakPSourcePair p c Ω (potentialTorsion p c C a)
      (gradient (potentialTorsion p c C a)) := by
  have hu : ContDiff ℝ 1 (potentialTorsion p c C a) :=
    contDiff_one_flatContactPower (potential_torsion_exponent hp).1 _ _ _
  have hF : ContDiff ℝ 1
      (fun x => pFlux p (gradient (potentialTorsion p c C a) x)) := by
    have he : (fun x => pFlux p (gradient (potentialTorsion p c C a) x)) =
        fun x => (-(c/(n : ℝ))) • (x-a) := funext (pFlux_gradient_potentialTorsion hp hc hn C a)
    rw [he]
    have hi : ContDiff ℝ 1 (fun x : Space n => x-a) := contDiff_id.sub contDiff_const
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : Space n => -(c/(n : ℝ)))).smul hi
  refine ⟨hp,hΩ,locallySobolevPair_of_contDiffOn_one hp hΩ hu.contDiffOn,?_⟩
  intro D hD θ h hθ
  obtain ⟨hI,hDI,he⟩ := integral_inner_eq_neg_divergence_zeroBoundary_one hp hΩ hD hF.contDiffOn hθ
  refine ⟨hI,?_⟩
  change (∫ x in D, inner ℝ (pFlux p (gradient (potentialTorsion p c C a) x)) (h x)) = _
  rw [he]
  simp only [coordinateDivergence_flux_potentialTorsion hp hc hn C a,
    ←integral_const_mul,neg_mul,integral_neg,neg_neg]

/-- The profile has a genuine critical centre and exactly the regularity
assumptions used by the new critical-point comparison theorem. -/
theorem potentialTorsion_comparison_regularity {n : ℕ} {p c : ℝ}
    (hp : 1<p) (hc : 0<c) (hn : 2≤n) (C : ℝ) (a : Space n) :
    ContDiff ℝ 1 (potentialTorsion p c C a) ∧
    gradient (potentialTorsion p c C a) a=0 ∧
    (∀ x : Space n, gradient (potentialTorsion p c C a) x≠0 →
      ContDiffAt ℝ 2 (potentialTorsion p c C a) x) := by
  have hq := (potential_torsion_exponent hp).1
  have hu : ContDiff ℝ 1 (potentialTorsion p c C a) := contDiff_one_flatContactPower hq _ _ _
  have hzero : gradient (potentialTorsion p c C a) a=0 := by
    unfold potentialTorsion
    rw [gradient_flatContactPower hq]
    simp only [sub_self,gradient_criticalPowerPenalty_zero hq,smul_zero]
  refine ⟨hu,hzero,?_⟩
  intro x hx
  have hxa : x-a≠0 := by
    intro h
    have he : x=a := sub_eq_zero.mp h
    exact hx (by rw [he,hzero])
  have hnorm : ContDiffAt ℝ ∞ (fun y : Space n => ‖y-a‖) x :=
    (contDiffAt_norm ℝ hxa).comp x (contDiffAt_id.sub contDiffAt_const)
  have hpow : ContDiffAt ℝ ∞ (fun y : Space n => ‖y-a‖^(p/(p-1))) x :=
    hnorm.rpow_const_of_ne (norm_ne_zero_iff.mpr hxa)
  have hfull : ContDiffAt ℝ ∞ (potentialTorsion p c C a) x := by
    unfold potentialTorsion flatContactPower criticalPowerPenalty
    exact (contDiffAt_const.mul (contDiffAt_const.mul hpow)).add contDiffAt_const
  exact hfull.of_le (by decide)

end BMCompactPDE
#print axioms BMCompactPDE.pFlux_gradient_potentialTorsion
#print axioms BMCompactPDE.coordinateDivergence_flux_potentialTorsion
#print axioms BMCompactPDE.weakPSourcePair_potentialTorsion
#print axioms BMCompactPDE.potentialTorsion_comparison_regularity
