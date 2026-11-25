import UpstreamGreenStrongClosure

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

/-- A common nonlinear flux pairing passes to a strong gradient limit.
The proof transfers the supporting lines of the actual Dirichlet energy and
differentiates the limiting energy in the same test direction. -/
theorem flux_pairing_constant_of_strong_Lp_limit {n : ℕ} {p J : ℝ} (hp : 1<p)
    {μ : Measure (Space n)} {g : ℕ→Space n→Space n} {G h : Space n→Space n}
    (hg : ∀ j, MemLp (g j) (ENNReal.ofReal p) μ) (hG : MemLp G (ENNReal.ofReal p) μ)
    (hh : MemLp h (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun j=>eLpNorm (g j-G) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    (hJ : ∀ᶠ j in atTop, (∫ x, inner ℝ (pFlux p (g j x)) (h x) ∂μ)=J) :
    (∫ x,inner ℝ (pFlux p (G x)) (h x) ∂μ)=J := by
  let : ENNReal.HolderConjugate (ENNReal.ofReal (p/(p-1))) (ENNReal.ofReal p) :=
    holderConjugate_p_dual hp
  let E := fun t : ℝ=>∫ x, ‖G x+t • h x‖^p ∂μ
  let A := fun t : ℝ=>E t - (p*J)*t
  have hmin : IsLocalMin A 0 := by
    apply Eventually.of_forall
    intro t
    have he := exterior_integral_energy_tendsto_of_Lp hp hg hG hlim
    have hlimt : Tendsto (fun j=>eLpNorm (fun x=>(g j x+t • h x)-(G x+t • h x))
        (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
      simpa only [add_sub_add_right_eq_sub,Pi.sub_def] using hlim
    have het := exterior_integral_energy_tendsto_of_Lp hp (fun j=>(hg j).add (hh.const_smul t))
      (hG.add (hh.const_smul t)) hlimt
    have hbound : (∫ x,‖G x‖^p ∂μ)+(p*J)*t ≤ E t := by
      apply le_of_tendsto_of_tendsto (he.add_const _) het
      filter_upwards [hJ] with j hj
      have hi := integrable_norm_rpow_of_memLp hp (hg j)
      have hk := inner_integrable_of_memLp (memLp_pFlux hp (hg j)) hh
      have hjt := integrable_norm_rpow_of_memLp hp ((hg j).add (hh.const_smul t))
      have hle := integral_mono (hi.add (hk.const_mul (p*t))) hjt (fun x=>by
        simpa only [Pi.add_apply,Pi.smul_apply,real_inner_smul_right,mul_assoc] using
          norm_rpow_add_tangent_lower hp (g j x) (t • h x))
      simpa only [integral_add hi (hk.const_mul (p*t)),integral_const_mul,hj,mul_right_comm p J t,
        Pi.add_apply,Pi.smul_apply] using hle
    simpa only [A,E,zero_smul,add_zero,mul_zero,sub_zero] using (le_sub_iff_add_le.mpr hbound)
  have hder : HasDerivAt A (p*(∫ x,inner ℝ (pFlux p (G x)) (h x) ∂μ)-p*J) 0 := by
    convert! (hasDerivAt_integral_energy_line hp hG hh).sub ((hasDerivAt_id (0:ℝ)).const_mul (p*J)) using 1
    simp only [mul_one]
  have hz := hmin.hasDerivAt_eq_zero hder
  exact (mul_left_cancel₀ (zero_lt_one.trans hp).ne' (sub_eq_zero.mp hz))

end BMCompactPDE
#print axioms BMCompactPDE.flux_pairing_constant_of_strong_Lp_limit
