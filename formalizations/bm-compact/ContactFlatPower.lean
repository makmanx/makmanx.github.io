import ContactForcedComparison

/-! A genuine isolated-critical step in the JLM doubling argument. Choosing
an even power slightly larger makes its actual nonlinear flux globally C1.
The full-W0 source comparison then forbids a flat lower contact, including at
zero gradient, and hence forbids coincident interior doubled maxima.
No theorem on sums or general viscosity comparison is assumed or concluded. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE


/-- The actual positive-source weak equation gives the strict numerical
viscosity lower-test inequality at noncritical C2 contacts, without C1(v). -/
theorem WeakPSourceSupersolutionPair.le_neg_classicalPLaplacian_at_strict_contact
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hvc : ContinuousOn v Ω)
    (hn : 2≤n) {x : Space n} (hx : x∈Ω)
    {φ : Space n → ℝ} (hφ : ContDiffOn ℝ 2 φ Ω)
    (htouch : v x=φ x) (hstrict : ∀ y∈Ω, y≠x → φ y<v y)
    (hg : gradient φ x≠0) :
    c ≤ -BMCompactAnalytic.classicalPLaplacian p φ x := by
  let U : Set (Space n) := Ω ∩ {y | gradient φ y≠0}
  have hU : IsOpen U := isOpen_noncritical_region_of_contDiffOn_two hv.2.1 hφ
  have hxU : x∈U := ⟨hx,hg⟩
  have hUΩ : U ⊆ Ω := inter_subset_left
  have hφU : ContDiffOn ℝ 2 φ U := hφ.mono hUΩ
  have hF : ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) U :=
    contDiffOn_pFlux_gradient_of_contDiffOn_two p hU hφU (fun _ hy => hy.2)
  have hi := (hv.mono hUΩ hU).le_neg_divergence_at_strict_contact (hvc.mono hUΩ)
    hn hxU (hφU.of_le (by norm_num)) hF htouch (fun y hy hne => hstrict y hy.1 hne)
  have hd := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
  have he : coordinateDivergence (fun y => pFlux p (gradient φ y)) x =
      BMCompactAnalytic.classicalPLaplacian p φ x := by
    unfold coordinateDivergence
    rw [←classicalDivergence_eq_sum_gradient_coordinates hd]
    exact classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
      (hφ.contDiffAt (hv.2.1.mem_nhds hx)) hg
  simpa only [he] using hi

def flatContactPower {n : ℕ} (q L A : ℝ) (a x : Space n) : ℝ :=
  (-L)*criticalPowerPenalty q (x-a)+A

theorem hasGradientAt_criticalPowerPenalty_sub {n : ℕ} {q : ℝ}
    (hq : 1<q) (a x : Space n) :
    HasGradientAt (fun y => criticalPowerPenalty q (y-a))
      (gradient (criticalPowerPenalty q : Space n → ℝ) (x-a)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! (hasGradientAt_criticalPowerPenalty (E := Space n) hq (x-a)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a) using 1 <;>
    simp [(hasGradientAt_criticalPowerPenalty (E := Space n) hq (x-a)).gradient]

theorem gradient_flatContactPower {n : ℕ} {q : ℝ} (hq : 1<q)
    (L A : ℝ) (a x : Space n) :
    gradient (flatContactPower q L A a) x =
      (-L) • gradient (criticalPowerPenalty q : Space n → ℝ) (x-a) := by
  change gradient (fun y => (-L)*criticalPowerPenalty q (y-a)+A) x = _
  rw [BMCompactAnalytic.gradient_add_const,BMCompactCapacityV2.gradient_const_mul,
    (hasGradientAt_criticalPowerPenalty_sub hq a x).gradient]

theorem contDiff_one_flatContactPower {n : ℕ} {q : ℝ} (hq : 1<q)
    (L A : ℝ) (a : Space n) : ContDiff ℝ 1 (flatContactPower q L A a) := by
  unfold flatContactPower criticalPowerPenalty
  exact (contDiff_const.mul (contDiff_const.mul
    ((contDiff_norm_rpow hq).comp (contDiff_id.sub contDiff_const)))).add contDiff_const

theorem contDiff_flatContactPower_even {n : ℕ} (k : ℕ)
    (L A : ℝ) (a : Space n) :
    ContDiff ℝ ∞ (flatContactPower ((2*k : ℕ) : ℝ) L A a) := by
  exact (contDiff_const.mul ((contDiff_criticalPowerPenalty_even (E := Space n) k).comp
    (contDiff_id.sub contDiff_const))).add contDiff_const

theorem pFlux_gradient_flatContactPower {n : ℕ} {p q : ℝ}
    (hp : 1<p) (hq : 1<q) (L A : ℝ) (a x : Space n) :
    pFlux p (gradient (flatContactPower q L A a) x) =
      (|-L|^(p-2)*(-L)) • (‖x-a‖^((q-1)*(p-1)-1) • (x-a)) := by
  rw [gradient_flatContactPower hq,pFlux_smul,pFlux_gradient_criticalPowerPenalty hp hq]

theorem contDiff_one_flux_flatContactPower {n : ℕ} {p q : ℝ}
    (hp : 1<p) (hq : 1<q) (hs : 1<(q-1)*(p-1)-1)
    (L A : ℝ) (a : Space n) :
    ContDiff ℝ 1 (fun x => pFlux p (gradient (flatContactPower q L A a) x)) := by
  have heq : (fun x => pFlux p (gradient (flatContactPower q L A a) x)) =
      fun x => (|-L|^(p-2)*(-L)) • (‖x-a‖^((q-1)*(p-1)-1) • (x-a)) :=
    funext (pFlux_gradient_flatContactPower hp hq L A a)
  rw [heq]
  have hshift : ContDiff ℝ 1 (fun x : Space n => x-a) := contDiff_id.sub contDiff_const
  have hnorm : ContDiff ℝ 1 (fun x : Space n => ‖x-a‖^((q-1)*(p-1)-1)) :=
    (contDiff_norm_rpow (E := Space n) hs).comp hshift
  have hscalar : ContDiff ℝ 1 (fun _ : Space n => (|-L|^(p-2)*(-L))) := contDiff_const
  exact hscalar.smul (hnorm.smul hshift)

theorem coordinateDivergence_flux_flatContactPower_pole {n : ℕ} {p q : ℝ}
    (hp : 1<p) (hq : 1<q) (hs : 0<(q-1)*(p-1)-1)
    (L A : ℝ) (a : Space n) :
    coordinateDivergence (fun x => pFlux p (gradient (flatContactPower q L A a) x)) a=0 := by
  have hd : HasFDerivAt
      (fun x : Space n => (|-L|^(p-2)*(-L)) •
        (‖x-a‖^((q-1)*(p-1)-1) • (x-a))) (0 : Space n →L[ℝ] Space n) a := by
    have hzbase : HasFDerivAt (fun z : Space n => ‖z‖^((q-1)*(p-1)-1) • z)
        (0 : Space n →L[ℝ] Space n) (a-a) := by
      simpa only [sub_self] using hasFDerivAt_criticalRadialFlux_zero (E := Space n) hs
    have hz := hzbase.comp (f := fun x : Space n => x-a) a ((hasFDerivAt_id a).sub_const a)
    simpa only [sub_self,ContinuousLinearMap.zero_comp,smul_zero] using!
      hz.const_smul (|-L|^(p-2)*(-L))
  have heq : (fun x => pFlux p (gradient (flatContactPower q L A a) x)) =
      fun x => (|-L|^(p-2)*(-L)) • (‖x-a‖^((q-1)*(p-1)-1) • (x-a)) :=
    funext (pFlux_gradient_flatContactPower hp hq L A a)
  rw [heq]
  unfold coordinateDivergence
  rw [←classicalDivergence_eq_sum_gradient_coordinates hd.differentiableAt]
  unfold classicalDivergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.toLinearMap_zero,map_zero]

theorem WeakPSourceSupersolutionPair.no_flat_power_lower_bound
    {n : ℕ} {p c q : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hc : 0<c)
    (hvc : ContinuousOn v Ω) (hn : 2≤n) (hq : 1<q)
    (hs : 1<(q-1)*(p-1)-1) {a : Space n} (ha : a∈Ω) (j : ℝ) :
    ¬ (∀ y∈Ω, v a-j*criticalPowerPenalty q (y-a)≤v y) := by
  intro hbound
  let φ : Space n → ℝ := flatContactPower q (j+1) (v a) a
  have hφ : ContDiff ℝ 1 φ := contDiff_one_flatContactPower hq _ _ _
  have hF : ContDiff ℝ 1 (fun y => pFlux p (gradient φ y)) :=
    contDiff_one_flux_flatContactPower hv.1 hq hs _ _ _
  have hq0 : q≠0 := (zero_lt_one.trans hq).ne'
  have htouch : v a=φ a := by
    simp only [φ,flatContactPower,criticalPowerPenalty,sub_self,norm_zero,
      Real.zero_rpow hq0,mul_zero,zero_add]
  have hstrict : ∀ y∈Ω, y≠a → φ y<v y := by
    intro y hy hya
    have hb := hbound y hy
    have hpow : 0<criticalPowerPenalty q (y-a) :=
      criticalPowerPenalty_pos_of_ne_zero (zero_lt_one.trans hq) (sub_ne_zero.mpr hya)
    dsimp only [φ,flatContactPower]
    nlinarith
  have hineq := hv.le_neg_divergence_at_strict_contact hvc hn ha hφ.contDiffOn
    hF.contDiffOn htouch hstrict
  have hz : coordinateDivergence (fun y => pFlux p (gradient φ y)) a=0 :=
    coordinateDivergence_flux_flatContactPower_pole hv.1 hq (zero_lt_one.trans hs) _ _ _
  rw [hz,neg_zero] at hineq
  exact (not_le.mpr hc) hineq

theorem WeakPSourceSupersolutionPair.ne_of_doubled_maximum
    {n : ℕ} {p c q : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hc : 0<c)
    (hvc : ContinuousOn v Ω) (hn : 2≤n) (hq : 1<q)
    (hs : 1<(q-1)*(p-1)-1) (u : Space n → ℝ) (j : ℝ)
    {x y : Space n} (hx : x∈Ω) (_hy : y∈Ω)
    (hmax : ∀ z∈Ω, ∀ w∈Ω,
      u z-v w-j*criticalPowerPenalty q (z-w) ≤
        u x-v y-j*criticalPowerPenalty q (x-y)) : x≠y := by
  intro hxy
  subst y
  apply hv.no_flat_power_lower_bound hc hvc hn hq hs hx j
  intro w hw
  have hh := hmax x hx w hw
  have hq0 : q≠0 := (zero_lt_one.trans hq).ne'
  have hp0 : criticalPowerPenalty q (x-x)=0 := by
    simp only [criticalPowerPenalty,sub_self,norm_zero,Real.zero_rpow hq0,mul_zero]
  have he : criticalPowerPenalty q (x-w)=criticalPowerPenalty q (w-x) := by
    simp only [criticalPowerPenalty,norm_sub_rev]
  rw [hp0,mul_zero,sub_zero,he] at hh
  linarith

theorem exists_even_flat_contact_exponent {p : ℝ} (hp : 1<p) :
    ∃ k : ℕ, 2≤k ∧ 1<((((2*k : ℕ) : ℝ)-1)*(p-1)-1) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2 : ℝ) ((p+1)/(p-1)))
  have hk2 : (2 : ℝ)<(k : ℝ) := (le_max_left _ _).trans_lt hk
  have hq : (p+1)/(p-1)<((2*k : ℕ) : ℝ) := by
    have hh := (le_max_right (2 : ℝ) ((p+1)/(p-1))).trans_lt hk
    push_cast
    nlinarith
  refine ⟨k,?_,?_⟩
  · have hh : 2<k := by exact_mod_cast hk2
    exact hh.le
  · have hh := (div_lt_iff₀ (sub_pos.mpr hp)).mp hq
    nlinarith

/-- The actual forced weak equation excludes coincident doubled maxima for
one genuine C-infinity even power chosen for every p>1. -/
theorem WeakPSourcePair.exists_even_power_doubled_maximum_ne
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourcePair p c Ω v h) (hc : 0<c)
    (hvc : ContinuousOn v Ω) (hn : 2≤n) :
    ∃ k : ℕ, 2≤k ∧ ContDiff ℝ ∞ (criticalPowerPenalty ((2*k : ℕ) : ℝ) : Space n → ℝ) ∧
      ∀ (u : Space n → ℝ) (j : ℝ) (x y : Space n), x∈Ω → y∈Ω →
        (∀ z∈Ω, ∀ w∈Ω,
          u z-v w-j*criticalPowerPenalty ((2*k : ℕ) : ℝ) (z-w) ≤
            u x-v y-j*criticalPowerPenalty ((2*k : ℕ) : ℝ) (x-y)) → x≠y := by
  obtain ⟨k,hk,hs⟩ := exists_even_flat_contact_exponent hv.1
  have hq : 1<((2*k : ℕ) : ℝ) := by
    have hh : (2 : ℝ)≤(k : ℝ) := by exact_mod_cast hk
    push_cast
    linarith
  refine ⟨k,hk,contDiff_criticalPowerPenalty_even k,?_⟩
  intro u j x y hx hy hmax
  exact hv.supersolution.ne_of_doubled_maximum hc hvc hn hq hs u j hx hy hmax

end BMCompactPDE
#print axioms BMCompactPDE.hasGradientAt_criticalPowerPenalty_sub
#print axioms BMCompactPDE.gradient_flatContactPower
#print axioms BMCompactPDE.contDiff_one_flatContactPower
#print axioms BMCompactPDE.contDiff_flatContactPower_even
#print axioms BMCompactPDE.pFlux_gradient_flatContactPower
#print axioms BMCompactPDE.contDiff_one_flux_flatContactPower
#print axioms BMCompactPDE.coordinateDivergence_flux_flatContactPower_pole
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.no_flat_power_lower_bound
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.ne_of_doubled_maximum
#print axioms BMCompactPDE.exists_even_flat_contact_exponent
#print axioms BMCompactPDE.WeakPSourcePair.exists_even_power_doubled_maximum_ne
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.le_neg_classicalPLaplacian_at_strict_contact
