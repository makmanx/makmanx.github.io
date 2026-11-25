import GradientAnalyticBatch

/-! In the singular range, an actual weak same-source difference controls
the unweighted p-energy of the gradient difference. Weighted coercivity,
Hölder interpolation, and the full Sobolev cutoff identity supply the estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem singular_factorization {p t r d : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hd : 0 ≤ d) (hdr : d ≤ r) :
    (t * ((p-1) * r^(p-2) * d^2))^(p/2) * (t*r^p)^(1-p/2) =
      (p-1)^(p/2) * (t*d^p) := by
  have ha : 0 < p/2 := by linarith
  have hb : 0 < 1-p/2 := by linarith
  have hp0 : 0 < p := by linarith
  rcases hr.eq_or_lt with hrz | hrp
  · have hdz : d = 0 := by linarith
    subst r
    subst d
    simp [Real.zero_rpow ha.ne', Real.zero_rpow hp0.ne']
  have hw := Real.rpow_nonneg hr (p-2)
  have hpm := sub_nonneg.mpr hp.le
  rw [Real.mul_rpow ht (mul_nonneg (mul_nonneg hpm hw) (sq_nonneg d)),
    Real.mul_rpow (mul_nonneg hpm hw) (sq_nonneg d), Real.mul_rpow hpm hw,
    ← Real.rpow_two d, ← Real.rpow_mul hd, ← Real.rpow_mul hr,
    Real.mul_rpow ht (Real.rpow_nonneg hr p), ← Real.rpow_mul hr]
  have h₁ : t^(p/2) * t^(1-p/2) = t := by
    rw [← Real.rpow_add_of_nonneg ht ha.le hb.le, show p/2+(1-p/2)=1 by ring, Real.rpow_one]
  have h₂ : r^((p-2)*(p/2)) * r^(p*(1-p/2)) = 1 := by
    rw [← Real.rpow_add hrp, show (p-2)*(p/2) + p*(1-p/2) = 0 by ring, Real.rpow_zero]
  rw [show 2*(p/2)=p by ring]
  calc
    _ = ((t^(p/2)*t^(1-p/2)) * (r^((p-2)*(p/2))*r^(p*(1-p/2)))) *
          ((p-1)^(p/2)*d^p) := by ring
    _ = _ := by rw [h₁,h₂]; ring

/-- Two actual weak solutions with the same constant source in 1<p<2
satisfy an unweighted p-energy estimate. All energies are obtained from their
actual Sobolev data and the nonnegative smooth cutoff. -/
theorem WeakPSourcePair.local_unweighted_gradient_difference_singular
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hp2 : p < 2) (hD : LocalDomain D Ω) {χ : Space n → ℝ}
    (hχ : SmoothTest D χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun x => χ x * ‖g x - h x‖^p) (volume.restrict D) ∧
    Integrable (fun x => χ x * (‖g x‖+‖h x‖)^p) (volume.restrict D) ∧
    (p-1)^(p/2) * (∫ x in D, χ x * ‖g x-h x‖^p) ≤
      (-(∫ x in D, (u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)))^(p/2) *
        (∫ x in D, χ x*(‖g x‖+‖h x‖)^p)^(1-p/2) := by
  have hp := hu.1
  have hp0 : 0 < p := zero_lt_one.trans hp
  have ha : 0 < p/2 := by linarith
  have hb : 0 < 1-p/2 := by linarith
  let μ := volume.restrict D
  let W := fun x => χ x * ((p-1)*(‖g x‖+‖h x‖)^(p-2)*‖g x-h x‖^2)
  let S := fun x => χ x * (‖g x‖+‖h x‖)^p
  let I := fun x => χ x * ‖g x-h x‖^p
  have hW0 (x) : 0 ≤ W x := mul_nonneg (hχ0 x) (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hp.le) (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _))
    (sq_nonneg _))
  have hS0 (x) : 0 ≤ S x := mul_nonneg (hχ0 x) (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  have hI0 (x) : 0 ≤ I x := mul_nonneg (hχ0 x) (Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨hWI, hbound⟩ := hu.local_weighted_gradient_difference_bound hv hp2.le hD hχ hχ0
  change Integrable W μ at hWI
  change (∫ x, W x ∂μ) ≤ _ at hbound
  have hg := (hu.2.2.1 D hD).2.2.1
  have hh := (hv.2.2.1 D hD).2.2.1
  have htop : MemLp χ (∞ : ℝ≥0∞) μ := hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _
  have hII : Integrable I μ := by
    simpa only [I, Pi.sub_apply, Pi.mul_apply, mul_comm] using!
      (integrable_norm_rpow_of_memLp hp (hg.sub hh)).mul_of_top_right htop
  have hSI : Integrable S μ := by
    have hR := (hg.norm.add hh.norm).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    have hi : Integrable (fun x => (‖g x‖+‖h x‖)^p) μ := by
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        ENNReal.toReal_ofReal hp0.le] using hR
    simpa only [S, Pi.mul_apply, mul_comm] using! hi.mul_of_top_right htop
  refine ⟨hII,hSI,?_⟩
  have e (x) : W x ^ (p/2) * S x ^ (1-p/2) = (p-1)^(p/2) * I x :=
    singular_factorization hp hp2 (hχ0 x) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _) (norm_sub_le _ _)
  have hC : 0 ≤ (p-1)^(p/2) := Real.rpow_nonneg (sub_nonneg.mpr hp.le) _
  have hR0 : 0 ≤ ∫ x, W x ∂μ := integral_nonneg (fun x => hW0 x)
  have hT0 : 0 ≤ ∫ x, S x ∂μ := integral_nonneg (fun x => hS0 x)
  have hInt : (p-1)^(p/2) * (∫ x, I x ∂μ) ≤ (∫ x, W x ∂μ)^(p/2) * (∫ x,S x ∂μ)^(1-p/2) := by
    have H := ENNReal.lintegral_mul_norm_pow_le (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hWI.1.aemeasurable)
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hSI.1.aemeasurable) ha.le hb.le (by ring)
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0 _))).mp
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hII.const_mul _)
      (Eventually.of_forall (fun x => mul_nonneg hC (hI0 x))),
      ENNReal.ofReal_mul (Real.rpow_nonneg hR0 _), ← ENNReal.ofReal_rpow_of_nonneg hR0 ha.le,
      ← ENNReal.ofReal_rpow_of_nonneg hT0 hb.le, ofReal_integral_eq_lintegral_ofReal hWI (Eventually.of_forall hW0),
      ofReal_integral_eq_lintegral_ofReal hSI (Eventually.of_forall hS0)]
    convert H using 1
    apply lintegral_congr
    intro x
    simp only [← e, Function.comp_apply, ENNReal.ofReal_mul (Real.rpow_nonneg (hW0 x) _),
      ← ENNReal.ofReal_rpow_of_nonneg (hW0 x) ha.le, ← ENNReal.ofReal_rpow_of_nonneg (hS0 x) hb.le]
    rfl
  exact hInt.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hR0 hbound ha.le)
    (Real.rpow_nonneg hT0 _))

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.local_unweighted_gradient_difference_singular
