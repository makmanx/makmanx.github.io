import TouchingGradient
import SupConvolutionProperties
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Module

/-! Printed Lemma4.2(b), including a genuine locally C² Taylor limit and
quadratic-curve second derivatives. All gradients and Hessians are actual
Mathlib derivatives; no PDE or second-order conclusion is postulated. -/
noncomputable section
set_option autoImplicit false
open Filter Set InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic

section


/-- Peano's second-order quotient for an actual locally C² real function. -/
theorem contDiffAt_two_second_quotient {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) :
    Tendsto (fun r : ℝ => (f r - f 0 - deriv f 0 * r) / r^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) 0 / 2)) := by
  obtain ⟨s,hs,hfs⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hs
  let I : Set ℝ := Ioo (-ε) ε
  have h0I : (0 : ℝ) ∈ I := ⟨by linarith, hε⟩
  have hIsub : I ⊆ s := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr hr
  have hI : I ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds h0I.1 h0I.2
  have ht := Real.taylor_tendsto (f := f) (n := 2) (s := I)
    (convex_Ioo (-ε) ε) h0I (hfs.mono hIsub)
  rw [nhdsWithin_eq_nhds.mpr hI] at ht
  have hcoef (r : ℝ) : taylorWithinEval f 2 I 0 r =
      f 0 + deriv f 0 * r + (deriv (deriv f) 0 / 2) * r^2 := by
    have h₁ : derivWithin f I 0 = deriv f 0 := derivWithin_of_mem_nhds hI
    have h₂ : iteratedDerivWithin 2 f I 0 = deriv (deriv f) 0 := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        (iteratedDerivWithin_of_isOpen (f := f) (n := 2) (s := I)
          (show IsOpen I from isOpen_Ioo) h0I)
    norm_num [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylor_within_zero_eval, h₁, h₂, iteratedDeriv_succ, iteratedDeriv_zero,
      smul_eq_mul]
    ring
  have ht' : Tendsto (fun r : ℝ =>
      (f r - (f 0 + deriv f 0 * r + (deriv (deriv f) 0 / 2) * r^2)) / r^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [hcoef, sub_zero] using ht.mono_left nhdsWithin_le_nhds
  have hadd := ht'.add_const (deriv (deriv f) 0 / 2)
  rw [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp
  ring

/-- The actual second derivatives obey the minimum comparison whenever the
values and first derivatives agree at a local touching point. -/
theorem min_le_second_derivative_of_local_min_comparison
    {f₁ f₂ f : ℝ → ℝ} (h₁ : ContDiffAt ℝ 2 f₁ 0)
    (h₂ : ContDiffAt ℝ 2 f₂ 0) (hf : ContDiffAt ℝ 2 f 0)
    (hv₁ : f₁ 0 = f 0) (hv₂ : f₂ 0 = f 0)
    (hd₁ : deriv f₁ 0 = deriv f 0) (hd₂ : deriv f₂ 0 = deriv f 0)
    (hcomp : ∀ᶠ r in 𝓝 (0 : ℝ), min (f₁ r) (f₂ r) ≤ f r) :
    min (deriv (deriv f₁) 0) (deriv (deriv f₂) 0) ≤ deriv (deriv f) 0 := by
  have hbound : min (deriv (deriv f₁) 0 / 2) (deriv (deriv f₂) 0 / 2) ≤
      deriv (deriv f) 0 / 2 := by
    apply le_of_tendsto_of_tendsto
      ((contDiffAt_two_second_quotient h₁).min (contDiffAt_two_second_quotient h₂))
      (contDiffAt_two_second_quotient hf)
    filter_upwards [hcomp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hpos
    rw [hv₁,hv₂,hd₁,hd₂, min_div_div_right (sq_nonneg r)]
    rw [min_sub_sub_right, min_sub_sub_right]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (sub_le_sub_right hr (f 0)) (deriv f 0 * r)) (sq_nonneg r)
  rw [min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)] at hbound
  linarith


end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic local perturbation, with no analyticity assumption. -/
def quadraticCurve (p u w : E) (r : ℝ) : E := p + r • u + r^2 • w

@[simp] theorem quadraticCurve_zero (p u w : E) : quadraticCurve p u w 0 = p := by
  simp [quadraticCurve]

/-- Actual first derivative of the quadratic perturbation. -/
theorem quadraticCurve_hasDerivAt (p u w : E) (r : ℝ) :
    HasDerivAt (quadraticCurve p u w) (u + (2*r) • w) r := by
  simpa [quadraticCurve, two_mul] using!
    (((hasDerivAt_id r).smul_const u).const_add p).add
      (((hasDerivAt_id r).pow 2).smul_const w)

/-- Quadratic perturbations are C²; the order is finite, not analytic. -/
theorem quadraticCurve_contDiffAt (p u w : E) :
    ContDiffAt ℝ 2 (quadraticCurve p u w) 0 := by
  exact ((contDiffAt_const.add (contDiffAt_id.smul_const u)).add
    ((contDiffAt_id.pow 2).smul_const w))

/-- The first directional derivative along a quadratic perturbation. -/
theorem quadraticCurve_comp_deriv {f : E → ℝ} {p u w : E}
    (hf : DifferentiableAt ℝ f p) :
    deriv (fun r => f (quadraticCurve p u w r)) 0 = fderiv ℝ f p u := by
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (quadraticCurve_hasDerivAt p u w 0) (by simp)
  simpa using! h.deriv

/-- Chain rule for the actual second derivative along a quadratic path.
The Hessian is the derivative of the actual `fderiv`, not an extra tensor. -/
theorem quadraticCurve_comp_second_deriv {f : E → ℝ} {p u w : E}
    (hf : ContDiffAt ℝ 2 f p) :
    deriv (deriv (fun r => f (quadraticCurve p u w r))) 0 =
      fderiv ℝ (fderiv ℝ f) p u u + fderiv ℝ f p ((2 : ℝ) • w) := by
  let C : ℝ → E := quadraticCurve p u w
  let C' : ℝ → E := fun r => u + (2*r) • w
  have hC : HasDerivAt C u 0 := by
    simpa [C] using quadraticCurve_hasDerivAt p u w 0
  have hC' : HasDerivAt C' ((2 : ℝ) • w) 0 := by
    simpa [C', two_mul] using
      (((hasDerivAt_id (0 : ℝ)).const_mul 2).smul_const w).const_add u
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hD : HasDerivAt (fun r => fderiv ℝ f (C r))
      (fderiv ℝ (fderiv ℝ f) p u) 0 := by
    simpa only [Function.comp_apply] using!
      hf'.comp_hasDerivAt_of_eq 0 hC (by simp [C])
  have hprod := hD.clm_apply hC'
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ),
      deriv (fun r => f (C r)) r = fderiv ℝ f (C r) (C' r) := by
    have hlocal : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q :=
      (hf.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
    have hpath : Tendsto C (𝓝 (0 : ℝ)) (𝓝 p) := by
      simpa [C] using hC.continuousAt.tendsto
    filter_upwards [hpath.eventually hlocal] with r hr
    have hh := hr.hasFDerivAt.comp_hasDerivAt r (quadraticCurve_hasDerivAt p u w r)
    simpa [C,C'] using! hh.deriv
  have hh := hprod.congr_of_eventuallyEq hnear
  simpa [C,C'] using! hh.deriv


end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual Hessian as a continuous bilinear form. -/
def actualHessian (f : E → ℝ) (p : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) p

/-- The Hessian comparison from a local touching inequality, with proportional
first derivatives. The wrapper below derives proportionality from touching. -/
theorem touching_hessian_of_proportional {t α β : ℝ}
    {v₁ v₂ φ : E → ℝ} {y z x : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : ContDiffAt ℝ 2 v₁ y) (h₂ : ContDiffAt ℝ 2 v₂ z)
    (hφ : ContDiffAt ℝ 2 φ x) (hL₁ : fderiv ℝ v₁ y ≠ 0)
    (hA : fderiv ℝ φ x = α • fderiv ℝ v₁ y)
    (hB : fderiv ℝ φ x = β • fderiv ℝ v₂ z)
    (hnorm : t*α + (1-t)*β = 1)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) (e : E) :
    t*α^3 * actualHessian v₁ y e e +
      (1-t)*β^3 * actualHessian v₂ z e e ≤ actualHessian φ x e e := by
  have hex : ∃ n : E, fderiv ℝ v₁ y n ≠ 0 := by
    by_contra h
    apply hL₁
    ext n
    have hh : ¬ fderiv ℝ v₁ y n ≠ 0 := fun hn => h ⟨n,hn⟩
    exact not_ne_iff.mp hh
  obtain ⟨n₀,hn₀⟩ := hex
  let n : E := (-(fderiv ℝ v₁ y n₀)⁻¹) • n₀
  have hn : fderiv ℝ v₁ y n = -1 := by
    simp [n, map_smul, smul_eq_mul, hn₀]
  have hφn : fderiv ℝ φ x n = -α := by
    rw [hA]
    simp [hn]
  let A : ℝ := actualHessian v₁ y e e
  let B : ℝ := actualHessian v₂ z e e
  let C : ℝ := actualHessian φ x e e
  let κ : ℝ := (α^2*A - β^2*B)/2
  let Y : ℝ → E := quadraticCurve y (α • e) (κ • n)
  let Z : ℝ → E := quadraticCurve z (β • e) 0
  let X : ℝ → E := quadraticCurve x e ((t*κ) • n)
  have hpath (r : ℝ) : t • Y r + (1-t) • Z r = X r := by
    dsimp [Y,Z,X,quadraticCurve]
    rw [hx]
    have hm := congrArg (fun s : ℝ => r*s) hnorm
    match_scalars <;> nlinarith only [hm]
  have hY : ContDiffAt ℝ 2 (fun r => v₁ (Y r)) 0 := by
    have hh : ContDiffAt ℝ 2 v₁ (Y 0) := by simpa [Y] using h₁
    simpa only [Function.comp_apply] using! hh.comp 0 (quadraticCurve_contDiffAt y (α • e) (κ • n))
  have hZ : ContDiffAt ℝ 2 (fun r => v₂ (Z r)) 0 := by
    have hh : ContDiffAt ℝ 2 v₂ (Z 0) := by simpa [Z] using h₂
    simpa only [Function.comp_apply] using! hh.comp 0 (quadraticCurve_contDiffAt z (β • e) 0)
  have hX : ContDiffAt ℝ 2 (fun r => φ (X r)) 0 := by
    have hh : ContDiffAt ℝ 2 φ (X 0) := by simpa [X] using hφ
    simpa only [Function.comp_apply] using! hh.comp 0 (quadraticCurve_contDiffAt x e ((t*κ) • n))
  have hdY : deriv (fun r => v₁ (Y r)) 0 = deriv (fun r => φ (X r)) 0 := by
    rw [quadraticCurve_comp_deriv (h₁.differentiableAt (by norm_num)),
      quadraticCurve_comp_deriv (hφ.differentiableAt (by norm_num))]
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L e) hA
    simpa [map_smul,smul_eq_mul] using hh.symm
  have hdZ : deriv (fun r => v₂ (Z r)) 0 = deriv (fun r => φ (X r)) 0 := by
    rw [quadraticCurve_comp_deriv (h₂.differentiableAt (by norm_num)),
      quadraticCurve_comp_deriv (hφ.differentiableAt (by norm_num))]
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L e) hB
    simpa [map_smul,smul_eq_mul] using hh.symm
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ),
      min (v₁ (Y r)) (v₂ (Z r)) ≤ φ (X r) := by
    have hp : Tendsto (fun r => (Y r,Z r)) (𝓝 (0 : ℝ)) (𝓝 (y,z)) := by
      simpa [Y,Z] using
        ((quadraticCurve_contDiffAt y (α • e) (κ • n)).continuousAt.tendsto.prodMk_nhds
          (quadraticCurve_contDiffAt z (β • e) 0).continuousAt.tendsto)
    filter_upwards [hp.eventually htouch] with r hr
    simpa only [hpath] using hr
  have hb := min_le_second_derivative_of_local_min_comparison hY hZ hX
    (by simpa [Y,X] using hv₁) (by simpa [Z,X] using hv₂) hdY hdZ hevent
  have hYY : deriv (deriv (fun r => v₁ (Y r))) 0 = α^2*A - 2*κ := by
    rw [quadraticCurve_comp_second_deriv h₁]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hn]
    dsimp [A,actualHessian]
    ring
  have hZZ : deriv (deriv (fun r => v₂ (Z r))) 0 = β^2*B := by
    rw [quadraticCurve_comp_second_deriv h₂]
    simp only [map_smul, smul_apply, smul_eq_mul,smul_zero,
      map_zero,add_zero]
    dsimp [B,actualHessian]
    ring
  have hXX : deriv (deriv (fun r => φ (X r))) 0 = C - 2*t*α*κ := by
    rw [quadraticCurve_comp_second_deriv hφ]
    simp only [map_smul, smul_eq_mul]
    rw [hφn]
    dsimp [C,actualHessian]
    ring
  have hκ : α^2*A - 2*κ = β^2*B := by dsimp [κ]; ring
  rw [hYY,hZZ,hXX,hκ,min_self] at hb
  have hm := congrArg (fun s : ℝ => s*β^2*B) hnorm
  dsimp [κ] at hb
  change t*α^3*A + (1-t)*β^3*B ≤ C
  nlinarith only [hb,hm]

/-- Cubic Hessian weights and positive first-derivative proportionality are
both derived from the actual C² local touching hypotheses. -/
theorem local_touching_hessian_cubic_weights {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {v₁ v₂ φ : E → ℝ} {y z x : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : ContDiffAt ℝ 2 v₁ y) (h₂ : ContDiffAt ℝ 2 v₂ z)
    (hφ : ContDiffAt ℝ 2 φ x)
    (hL₁ : fderiv ℝ v₁ y ≠ 0) (hL₂ : fderiv ℝ v₂ z ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∃ α β : ℝ, 0<α ∧ 0<β ∧ fderiv ℝ φ x = α • fderiv ℝ v₁ y ∧
      fderiv ℝ φ x = β • fderiv ℝ v₂ z ∧ t*α+(1-t)*β=1 ∧
      ∀ e : E, t*α^3*actualHessian v₁ y e e +
        (1-t)*β^3*actualHessian v₂ z e e ≤ actualHessian φ x e e := by
  obtain ⟨α,β,hα,hβ,hA,hB,hnorm⟩ := touching_fderiv_positive_proportional ht ht1 hx
    (h₁.differentiableAt (by norm_num)).hasFDerivAt
    (h₂.differentiableAt (by norm_num)).hasFDerivAt
    (hφ.differentiableAt (by norm_num)).hasFDerivAt hL₁ hL₂ hv₁ hv₂ htouch
  exact ⟨α,β,hα,hβ,hA,hB,hnorm,
    touching_hessian_of_proportional hx h₁ h₂ hφ hL₁ hA hB hnorm hv₁ hv₂ htouch⟩


/-- A genuine local upper test for the actual supremum over decompositions
supplies the product-neighbourhood touching inequality. -/
theorem supConvolution_local_touching {t : ℝ} {v₁ v₂ φ : E → ℝ}
    {x y z : E} {m : ℝ} (hx : x = t • y + (1-t) • z)
    (hu : ∀ q, v₁ q ≤ m)
    (hupper : ∀ᶠ p in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ p ≤ φ p) :
    ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2) := by
  have hcont : Continuous (fun q : E × E => t • q.1 + (1-t) • q.2) :=
    (continuous_fst.const_smul t).add (continuous_snd.const_smul (1-t))
  have hp : Tendsto (fun q : E × E => t • q.1 + (1-t) • q.2)
      (𝓝 (y,z)) (𝓝 x) := by
    simpa only [←hx] using (hcont.continuousAt (x := (y,z))).tendsto
  filter_upwards [hp.eventually hupper] with q hq
  exact (BMCompactEnvelope.min_le_supConvolution_of_decomposition t hu rfl).trans hq

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Printed Lemma4.2(a,b): the unit normal, positive parameters, harmonic
reciprocal identity, and cubic-weight Hessian inequality all follow from an
actual locally C² touching pair with nonzero source gradients. -/
theorem local_touching_gradient_and_hessian {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {v₁ v₂ φ : E → ℝ} {y z x : E}
    (hx : x = t • y + (1-t) • z)
    (h₁ : ContDiffAt ℝ 2 v₁ y) (h₂ : ContDiffAt ℝ 2 v₂ z)
    (hφ : ContDiffAt ℝ 2 φ x)
    (hg₁ : gradient v₁ y ≠ 0) (hg₂ : gradient v₂ z ≠ 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) :
    ∃ (ν : E) (a b d : ℝ), ‖ν‖=1 ∧ 0<a ∧ 0<b ∧ 0<d ∧
      gradient v₁ y = (-a) • ν ∧ gradient v₂ z = (-b) • ν ∧
      gradient φ x = (-d) • ν ∧ 1/d = t/a+(1-t)/b ∧
      ∀ e : E, t*(d/a)^3*actualHessian v₁ y e e +
        (1-t)*(d/b)^3*actualHessian v₂ z e e ≤ actualHessian φ x e e := by
  have hd₁ := h₁.differentiableAt (by norm_num)
  have hd₂ := h₂.differentiableAt (by norm_num)
  have hdφ := hφ.differentiableAt (by norm_num)
  obtain ⟨α,β,hα,hβ,hA,hB,hnorm⟩ := touching_gradient_positive_proportional ht ht1
    hx hd₁.hasGradientAt hd₂.hasGradientAt hdφ.hasGradientAt hg₁ hg₂ hv₁ hv₂ htouch
  have hder₁ : fderiv ℝ v₁ y = toDual ℝ E (gradient v₁ y) := by
    simp [gradient]
  have hder₂ : fderiv ℝ v₂ z = toDual ℝ E (gradient v₂ z) := by
    simp [gradient]
  have hderφ : fderiv ℝ φ x = toDual ℝ E (gradient φ x) := by
    simp [gradient]
  have hLA : fderiv ℝ φ x = α • fderiv ℝ v₁ y := by
    rw [hderφ,hder₁]
    simpa only [map_smul] using congrArg (toDual ℝ E) hA
  have hLB : fderiv ℝ φ x = β • fderiv ℝ v₂ z := by
    rw [hderφ,hder₂]
    simpa only [map_smul] using congrArg (toDual ℝ E) hB
  have hL₁ : fderiv ℝ v₁ y ≠ 0 := by
    rw [hder₁]
    intro h
    apply hg₁
    apply (toDual ℝ E).injective
    simpa using h
  obtain ⟨ν,a,b,d,hν,ha,hb,hd,hgA,hgB,hgD,hrec⟩ :=
    unit_normal_of_positive_proportional hα hβ hg₁ hA hB hnorm
  have hng₁ : ‖gradient v₁ y‖ = a := by
    rw [hgA,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha,hν,mul_one]
  have hng₂ : ‖gradient v₂ z‖ = b := by
    rw [hgB,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hb,hν,mul_one]
  have hng : ‖gradient φ x‖ = d := by
    rw [hgD,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hd,hν,mul_one]
  have had : α = d/a := by
    apply (eq_div_iff ha.ne').mpr
    have hh := congrArg norm hA
    simpa [norm_smul,Real.norm_eq_abs,abs_of_pos hα,hng₁,hng] using hh.symm
  have hbd : β = d/b := by
    apply (eq_div_iff hb.ne').mpr
    have hh := congrArg norm hB
    simpa [norm_smul,Real.norm_eq_abs,abs_of_pos hβ,hng₂,hng] using hh.symm
  refine ⟨ν,a,b,d,hν,ha,hb,hd,hgA,hgB,hgD,hrec,?_⟩
  intro e
  rw [←had,←hbd]
  exact touching_hessian_of_proportional hx h₁ h₂ hφ hL₁ hLA hLB hnorm hv₁ hv₂ htouch e


/-- The exact gradient/Hessian consequence at a balanced maximizing pair of
the actual envelope, with a genuine local C² upper test. -/
theorem supConvolution_upper_test_gradient_and_hessian {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hu : ∀ q, v₁ q ≤ m)
    (h₁ : ContDiffAt ℝ 2 v₁ y) (h₂ : ContDiffAt ℝ 2 v₂ z)
    (hφ : ContDiffAt ℝ 2 φ x)
    (hg₁ : gradient v₁ y ≠ 0) (hg₂ : gradient v₂ z ≠ 0)
    (hv₁ : v₁ y = BMCompactEnvelope.supConvolution t v₁ v₂ x)
    (hv₂ : v₂ z = BMCompactEnvelope.supConvolution t v₁ v₂ x)
    (hcontact : BMCompactEnvelope.supConvolution t v₁ v₂ x = φ x)
    (hupper : ∀ᶠ p in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ p ≤ φ p) :
    ∃ (ν : E) (a b d : ℝ), ‖ν‖=1 ∧ 0<a ∧ 0<b ∧ 0<d ∧
      gradient v₁ y = (-a) • ν ∧ gradient v₂ z = (-b) • ν ∧
      gradient φ x = (-d) • ν ∧ 1/d = t/a+(1-t)/b ∧
      ∀ e : E, t*(d/a)^3*actualHessian v₁ y e e +
        (1-t)*(d/b)^3*actualHessian v₂ z e e ≤ actualHessian φ x e e :=
  local_touching_gradient_and_hessian ht ht1 hx h₁ h₂ hφ hg₁ hg₂
    (hv₁.trans hcontact) (hv₂.trans hcontact)
    (supConvolution_local_touching hx hu hupper)

end

end BMCompactAnalytic
#print axioms BMCompactAnalytic.contDiffAt_two_second_quotient
#print axioms BMCompactAnalytic.min_le_second_derivative_of_local_min_comparison
#print axioms BMCompactAnalytic.quadraticCurve_zero
#print axioms BMCompactAnalytic.quadraticCurve_hasDerivAt
#print axioms BMCompactAnalytic.quadraticCurve_contDiffAt
#print axioms BMCompactAnalytic.quadraticCurve_comp_deriv
#print axioms BMCompactAnalytic.quadraticCurve_comp_second_deriv
#print axioms BMCompactAnalytic.touching_hessian_of_proportional
#print axioms BMCompactAnalytic.local_touching_hessian_cubic_weights
#print axioms BMCompactAnalytic.local_touching_gradient_and_hessian

#print axioms BMCompactAnalytic.supConvolution_local_touching
#print axioms BMCompactAnalytic.supConvolution_upper_test_gradient_and_hessian
