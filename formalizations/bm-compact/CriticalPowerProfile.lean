import BMCompactChecked
import Mathlib.Analysis.InnerProductSpace.NormPow

/-! Actual power penalties at singular critical points, motivated by JLM
Proposition3.3. The actual nonlinear gradient flux is differentiable at the
critical pole and its actual divergence tends to zero when the power is chosen
above p/(p-1). Even powers give genuine global smooth tests. This is not the
theorem on sums or the general viscosity comparison theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace Asymptotics
open scoped Topology ContDiff
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def criticalPowerPenalty (q : ℝ) (x : E) : ℝ := q⁻¹*‖x‖^q

theorem hasGradientAt_criticalPowerPenalty {q : ℝ} (hq : 1 < q) (x : E) :
    HasGradientAt (criticalPowerPenalty q : E → ℝ) (‖x‖^(q-2) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (hasFDerivAt_norm_rpow x hq).const_mul q⁻¹
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  convert! hd using 1
  ext y
  simp only [criticalPowerPenalty,map_smul,toDual_apply_apply,real_inner_smul_left,
    smul_apply,smul_eq_mul]
  field_simp
  rfl

theorem gradient_criticalPowerPenalty {q : ℝ} (hq : 1 < q) (x : E) :
    gradient (criticalPowerPenalty q : E → ℝ) x = ‖x‖^(q-2) • x :=
  (hasGradientAt_criticalPowerPenalty hq x).gradient

theorem gradient_criticalPowerPenalty_zero {q : ℝ} (hq : 1 < q) :
    gradient (criticalPowerPenalty q : E → ℝ) 0 = 0 := by
  rw [gradient_criticalPowerPenalty hq]
  simp

theorem pFlux_gradient_criticalPowerPenalty {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (x : E) :
    pFlux p (gradient (criticalPowerPenalty q : E → ℝ) x) =
      ‖x‖^((q-1)*(p-1)-1) • x := by
  rw [gradient_criticalPowerPenalty hq]
  by_cases hx : x = 0
  · simp [hx]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [pFlux_nonneg_smul hp (Real.rpow_nonneg hr.le _),pFlux,smul_smul,
      ←Real.rpow_mul hr.le,←Real.rpow_add hr]
    congr 2
    ring

theorem criticalPowerFluxExponent_pos {p q : ℝ} (hp : 1 < p)
    (hq : p/(p-1) < q) : 0 < (q-1)*(p-1)-1 := by
  have hden : 0 < p-1 := sub_pos.mpr hp
  have h := (div_lt_iff₀ hden).mp hq
  nlinarith

/-- The vector factor removes the apparent singularity at the pole. -/
theorem hasFDerivAt_criticalRadialFlux_zero {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (fun x : E => ‖x‖^s • x) (0 : E →L[ℝ] E) 0 := by
  have hlim : Tendsto (fun x : E => ‖x‖^s) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : E => ‖x‖^s) :=
      (Real.continuous_rpow_const hs.le).comp continuous_norm
    simpa only [norm_zero,Real.zero_rpow hs.ne'] using (hc.continuousAt (x := (0 : E))).tendsto
  have ha : (fun x : E => ‖x‖^s) =o[𝓝 0] (fun _ : E => (1 : ℝ)) :=
    (isLittleO_const_iff (one_ne_zero : (1 : ℝ) ≠ 0)).mpr hlim
  have hv := ha.smul_isBigO (isBigO_refl (fun x : E => x) (𝓝 0))
  apply HasFDerivAt.of_isLittleO
  simpa only [norm_zero,smul_zero,sub_zero,map_zero,ContinuousLinearMap.zero_apply,zero_smul,one_smul] using hv

theorem hasFDerivAt_pFlux_gradient_criticalPowerPenalty_zero {p q : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hqp : p/(p-1) < q) :
    HasFDerivAt (fun x : E => pFlux p (gradient (criticalPowerPenalty q) x))
      (0 : E →L[ℝ] E) 0 := by
  have heq : (fun x : E => pFlux p (gradient (criticalPowerPenalty q) x)) =
      (fun x : E => ‖x‖^((q-1)*(p-1)-1) • x) :=
    funext (pFlux_gradient_criticalPowerPenalty hp hq)
  rw [heq]
  exact hasFDerivAt_criticalRadialFlux_zero (criticalPowerFluxExponent_pos hp hqp)

theorem hasFDerivAt_gradient_criticalPowerPenalty_zero {q : ℝ} (hq : 2 < q) :
    HasFDerivAt (gradient (criticalPowerPenalty q : E → ℝ)) (0 : E →L[ℝ] E) 0 := by
  have hq1 : 1 < q := lt_trans (by norm_num) hq
  have heq : gradient (criticalPowerPenalty q : E → ℝ) =
      (fun x : E => ‖x‖^(q-2) • x) := funext (gradient_criticalPowerPenalty hq1)
  rw [heq]
  exact hasFDerivAt_criticalRadialFlux_zero (sub_pos.mpr hq)

theorem contDiff_criticalPowerPenalty_even (k : ℕ) :
    ContDiff ℝ ∞ (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) := by
  have heq : (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) =
      fun x : E => (((2*k : ℕ) : ℝ))⁻¹*(‖x‖^2)^k := by
    funext x
    simp only [criticalPowerPenalty,Real.rpow_natCast,pow_mul]
  rw [heq]
  exact contDiff_const.mul ((contDiff_norm_sq ℝ).pow k)

theorem exists_even_criticalPowerPenalty_exponent (p : ℝ) :
    ∃ k : ℕ, 2 ≤ k ∧ max 2 (p/(p-1)) < ((2*k : ℕ) : ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2 : ℝ) (p/(p-1)))
  have hk2 : (2 : ℝ) < (k : ℝ) := (le_max_left _ _).trans_lt hk
  refine ⟨k,?_,?_⟩
  · have hkn : 2 < k := by exact_mod_cast hk2
    exact hkn.le
  · push_cast
    nlinarith

section Finite
variable [FiniteDimensional ℝ E]

theorem classicalDivergence_pFlux_gradient_criticalPowerPenalty {p q : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hqp : p/(p-1) < q) (x : E) :
    classicalDivergence (fun y : E => pFlux p (gradient (criticalPowerPenalty q) y)) x =
      ((Module.finrank ℝ E : ℝ)+(q-1)*(p-1)-1)*‖x‖^((q-1)*(p-1)-1) := by
  by_cases hx : x = 0
  · subst x
    unfold classicalDivergence
    rw [(hasFDerivAt_pFlux_gradient_criticalPowerPenalty_zero hp hq hqp).fderiv]
    simp only [ContinuousLinearMap.toLinearMap_zero,map_zero,norm_zero,
      Real.zero_rpow (criticalPowerFluxExponent_pos hp hqp).ne',mul_zero]
  · have heq : (fun y : E => pFlux p (gradient (criticalPowerPenalty q) y)) =
        (fun y : E => ‖y‖^((q-1)*(p-1)-1) • y) :=
      funext (pFlux_gradient_criticalPowerPenalty hp hq)
    rw [heq,classicalDivergence_norm_rpow_smul _ hx]
    congr 1
    ring

theorem tendsto_classicalDivergence_pFlux_gradient_criticalPowerPenalty_zero {p q : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hqp : p/(p-1) < q) :
    Tendsto (fun x : E =>
      classicalDivergence (fun y : E => pFlux p (gradient (criticalPowerPenalty q) y)) x)
      (𝓝[≠] (0 : E)) (𝓝 0) := by
  have hs := criticalPowerFluxExponent_pos hp hqp
  have hc : Continuous (fun x : E =>
      ((Module.finrank ℝ E : ℝ)+(q-1)*(p-1)-1)*‖x‖^((q-1)*(p-1)-1)) :=
    continuous_const.mul ((Real.continuous_rpow_const hs.le).comp continuous_norm)
  have ht := (hc.continuousAt (x := (0 : E))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := ({(0 : E)}ᶜ)))
  simpa only [classicalDivergence_pFlux_gradient_criticalPowerPenalty hp hq hqp,
    norm_zero,Real.zero_rpow hs.ne',mul_zero] using ht

end Finite
end BMCompactPDE
#print axioms BMCompactPDE.hasGradientAt_criticalPowerPenalty
#print axioms BMCompactPDE.gradient_criticalPowerPenalty
#print axioms BMCompactPDE.gradient_criticalPowerPenalty_zero
#print axioms BMCompactPDE.pFlux_gradient_criticalPowerPenalty
#print axioms BMCompactPDE.criticalPowerFluxExponent_pos
#print axioms BMCompactPDE.hasFDerivAt_criticalRadialFlux_zero
#print axioms BMCompactPDE.hasFDerivAt_pFlux_gradient_criticalPowerPenalty_zero
#print axioms BMCompactPDE.hasFDerivAt_gradient_criticalPowerPenalty_zero
#print axioms BMCompactPDE.contDiff_criticalPowerPenalty_even
#print axioms BMCompactPDE.exists_even_criticalPowerPenalty_exponent
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_criticalPowerPenalty
#print axioms BMCompactPDE.tendsto_classicalDivergence_pFlux_gradient_criticalPowerPenalty_zero
