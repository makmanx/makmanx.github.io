import UpstreamFundamentalPolar
import UpstreamFundamentalIntegrability

/-! Exact singular-source integration for the actual radial flux. The final
fundamental profile uses the concrete polar sphere mass,not a free sigma,and
satisfies the manuscript sign integral flux.grad(test)=-test(0). This does not
assert W1,p membership of the critical logarithmic profile through its pole. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- Actual integration computes the mass of the radial source flux,including
its sign and the full concrete Euclidean sphere factor,for every smooth compact
test. The mass is derived by polar integration and raywise FTC. -/
theorem integral_radialSourceFlux_gradient_test {n : ℕ} (hn : 0<n) (σ : ℝ)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x,inner ℝ (radialSourceFlux n σ x) (gradient φ x)) =
      -(canonicalSphereArea n/σ)*φ 0 := by
  have hi := integrable_radialSourceFlux_gradient_test hn σ hφ hc
  rw [integral_eq_sphere_ray hn hi]
  have hinner (θ : sphere (0 : Space n) 1) :
      (∫ r in Ioi (0 : ℝ),r^(n-1)*
        inner ℝ (radialSourceFlux n σ (r • (θ : Space n))) (gradient φ (r • (θ : Space n)))) =
      σ⁻¹*(-φ 0) := by
    have hθ : ‖(θ : Space n)‖=1 := mem_sphere_zero_iff_norm.mp θ.2
    calc
      _ = ∫ r in Ioi (0 : ℝ),σ⁻¹*inner ℝ (gradient φ (r • (θ : Space n))) (θ : Space n) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr0 : 0<r := hr
        have hJ : r^(n-1)*r^(-(n : ℝ))*r=1 := by
          conv_lhs => arg 2;rw [←Real.rpow_one r]
          rw [←Real.rpow_natCast,←Real.rpow_add hr0,←Real.rpow_add hr0]
          have he : ((n-1 : ℕ) : ℝ)+(-(n : ℝ))+1=0 := by
            rw [Nat.cast_sub (Nat.succ_le_iff.mpr hn),Nat.cast_one]
            ring
          rw [he,Real.rpow_zero]
        change r^(n-1)*inner ℝ (radialSourceFlux n σ (r • (θ : Space n)))
          (gradient φ (r • (θ : Space n))) =
          σ⁻¹*inner ℝ (gradient φ (r • (θ : Space n))) (θ : Space n)
        simp only [radialSourceFlux,norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hθ,mul_one,
          real_inner_smul_left]
        rw [real_inner_comm (gradient φ (r • (θ : Space n))) (θ : Space n)]
        calc
          _ = σ⁻¹*(r^(n-1)*r^(-(n : ℝ))*r)*
              inner ℝ (gradient φ (r • (θ : Space n))) (θ : Space n) := by ring
          _ = _ := by rw [hJ,mul_one]
      _ = σ⁻¹*(∫ r in Ioi (0 : ℝ),
          inner ℝ (gradient φ (r • (θ : Space n))) (θ : Space n)) := integral_const_mul _ _
      _ = _ := by
        rw [integral_ray_gradient (hφ.of_le (by simp)) hc hθ]
  simp_rw [hinner]
  rw [integral_const]
  change canonicalSphereArea n*(σ⁻¹*(-φ 0))=-(canonicalSphereArea n/σ)*φ 0
  ring

/-- The manuscript fundamental profile with the actual Euclidean polar sphere
normalization has a genuinely locally integrable flux through the pole and the
exact unit distributional source identity against every compact smooth test.
The sign is div(flux)=+delta_0,or minus-div(flux)=-delta_0. -/
theorem fundamentalPotential_unit_source {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hpn : (n : ℝ)≤p) :
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
  have hn1 : 1<(n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hσ := canonicalSphereArea_pos hn0
  have hAE : (fun x : Space n => pFlux p
      (gradient (fundamentalPotential n (canonicalSphereArea n) p) x)) =ᵐ[volume]
      radialSourceFlux n (canonicalSphereArea n) := by
    filter_upwards [Measure.ae_ne volume (0 : Space n)] with x hx
    exact pFlux_gradient_fundamentalPotential_all_p n hσ (hn1.trans_le hpn) hx
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

end BMCompactPDE
#print axioms BMCompactPDE.integral_radialSourceFlux_gradient_test
#print axioms BMCompactPDE.fundamentalPotential_unit_source
