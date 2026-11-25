import UpstreamFundamentalDistribution

/-! Canonical unit-source normalization for every real p>1, including the
subcritical range. Only the actual nonlinear flux is integrated through the
pole; no Sobolev membership of the potential or its gradient at the pole is
asserted. The sign is div(pFlux(gradient F))=delta_0. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- The actual canonically normalized fundamental profile has locally L1
nonlinear flux and unit distributional source for every p>1 in dimension at
least two. The concrete Euclidean polar sphere mass supplies the normalization,
and every compact smooth test gives integral flux.gradient(test)=-test(0). -/
theorem fundamentalPotential_unit_source_all_p {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hp : 1<p) :
    (∀ R : ℝ,IntegrableOn
      (fun x : Space n => pFlux p (gradient (fundamentalPotential n (canonicalSphereArea n) p) x))
      (ball 0 R) volume) ∧
    ∀ φ : Space n → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x => inner ℝ
        (pFlux p (gradient (fundamentalPotential n (canonicalSphereArea n) p) x)) (gradient φ x)) volume ∧
      (∫ x,inner ℝ (pFlux p (gradient (fundamentalPotential n (canonicalSphereArea n) p) x))
        (gradient φ x)) = -φ 0 := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hσ := canonicalSphereArea_pos hn0
  have hAE : (fun x : Space n => pFlux p
      (gradient (fundamentalPotential n (canonicalSphereArea n) p) x)) =ᵐ[volume]
      radialSourceFlux n (canonicalSphereArea n) := by
    filter_upwards [Measure.ae_ne volume (0 : Space n)] with x hx
    exact pFlux_gradient_fundamentalPotential_all_p n hσ hp hx
  refine ⟨?_,?_⟩
  · intro R
    exact (integrableOn_radialSourceFlux hn0 (canonicalSphereArea n) R).congr
      hAE.restrict.symm
  · intro φ hφ hc
    have he : (fun x => inner ℝ (pFlux p
        (gradient (fundamentalPotential n (canonicalSphereArea n) p) x)) (gradient φ x)) =ᵐ[volume]
        (fun x => inner ℝ (radialSourceFlux n (canonicalSphereArea n) x) (gradient φ x)) := by
      filter_upwards [hAE] with x hx
      rw [hx]
    refine ⟨(integrable_radialSourceFlux_gradient_test hn0 (canonicalSphereArea n) hφ hc).congr he.symm,?_⟩
    rw [integral_congr_ae he,integral_radialSourceFlux_gradient_test hn0 _ hφ hc,
      div_self hσ.ne',neg_one_mul]

/-- The positive subcritical sign convention, using the actual canonical
sphere normalization. This definition asserts no capacitary or Riesz measure
identification for a general compact set. -/
def positiveSubcriticalProfile (n : ℕ) (p : ℝ) (x : Space n) : ℝ :=
  -fundamentalPotential n (canonicalSphereArea n) p x

/-- For 1<p<n, the opposite signed profile is genuinely positive off its pole,
its actual nonlinear flux is locally L1 through the pole, and its compact-test
pairing equals +test(0). Thus minus-div(flux)=delta_0 with this convention. -/
theorem positiveSubcriticalProfile_unit_source {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hp : 1<p) (hpn : p<(n : ℝ)) :
    (∀ x : Space n,x≠0 → 0<positiveSubcriticalProfile n p x) ∧
    (∀ R : ℝ,IntegrableOn
      (fun x : Space n => pFlux p (gradient (positiveSubcriticalProfile n p) x))
      (ball 0 R) volume) ∧
    ∀ φ : Space n → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Integrable (fun x => inner ℝ
        (pFlux p (gradient (positiveSubcriticalProfile n p) x)) (gradient φ x)) volume ∧
      (∫ x,inner ℝ (pFlux p (gradient (positiveSubcriticalProfile n p) x))
        (gradient φ x)) = φ 0 := by
  have hσ := canonicalSphereArea_pos (lt_of_lt_of_le (by decide : 0<2) hn)
  have hF := fundamentalPotential_unit_source_all_p hn hp
  have hflux (x : Space n) : pFlux p (gradient (positiveSubcriticalProfile n p) x) =
      -pFlux p (gradient (fundamentalPotential n (canonicalSphereArea n) p) x) := by
    unfold positiveSubcriticalProfile gradient
    rw [fderiv_fun_neg,map_neg,pFlux_neg]
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hq : (p-(n : ℝ))/(p-1)<0 := div_neg_of_neg_of_pos (sub_neg.mpr hpn) (sub_pos.mpr hp)
    have hcoeff : ((p-(n : ℝ))/(p-1))⁻¹ * (canonicalSphereArea n)^(-(p-1)⁻¹)<0 :=
      mul_neg_of_neg_of_pos (inv_neg''.mpr hq) (Real.rpow_pos_of_pos hσ _)
    have hpower : 0<‖x‖^((p-(n : ℝ))/(p-1)) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _
    unfold positiveSubcriticalProfile fundamentalPotential
    rw [if_neg (ne_of_lt hpn)]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos hcoeff hpower)
  · intro R
    simpa only [hflux,Pi.neg_apply] using! (hF.1 R).neg
  · intro φ hφ hc
    obtain ⟨hi,he⟩ := hF.2 φ hφ hc
    constructor
    · simpa only [hflux,inner_neg_left,Pi.neg_apply] using! hi.neg
    · simp only [hflux,inner_neg_left,integral_neg,he,neg_neg]

end BMCompactPDE
#print axioms BMCompactPDE.fundamentalPotential_unit_source_all_p
#print axioms BMCompactPDE.positiveSubcriticalProfile_unit_source
