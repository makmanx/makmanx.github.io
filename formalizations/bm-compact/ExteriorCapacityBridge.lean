import ExteriorCondenserConstruction
import RootSobolevMultiplier
import WeakUniqueness
import CapacityAffineEnergy

/-! Concrete approximation tools for the capacity-energy comparison on
HKM printed pp.27-28 (PDF36-37). A.e. plateau data are imposed on an OPEN
neighborhood; they are never substituted for traces on a thin compact set. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- Strong convergence of actual Lp fields gives convergence of their actual
real p-energies; no convergence of energies is assumed. -/
theorem exterior_integral_energy_tendsto_of_Lp {n : ℕ} {p : ℝ} (hp : 1 < p)
    {μ : Measure (Space n)} {f : ℕ → Space n → Space n} {g : Space n → Space n}
    (hf : ∀ j, MemLp (f j) (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun j => eLpNorm (f j-g) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖f j x‖^p ∂μ) atTop (𝓝 (∫ x, ‖g x‖^p ∂μ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hl := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hlim
  have he (v : Space n → Space n) (hv : MemLp v (ENNReal.ofReal p) μ) :
      ‖hv.toLp v‖^p = ∫ x, ‖v x‖^p ∂μ := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    exact integral_congr_ae ((MemLp.coeFn_toLp hv).fun_comp (fun a => ‖a‖^p))
  have hn := ((continuous_norm.rpow_const
    (fun _ : Lp (Space n) (ENNReal.ofReal p) μ => Or.inr (zero_lt_one.trans hp).le)).tendsto
      (hg.toLp g)).comp hl
  simpa only [Function.comp_def, he] using hn

theorem SobolevPair.gradient_ae_zero_on_open_plateau {n : ℕ} {p : ℝ}
    {U O : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p O u g) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUO : U ⊆ O) (htrace : ∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) :
    g =ᵐ[volume.restrict U] (0 : Space n → Space n) := by
  have ht := ae_restrict_of_ae_restrict_of_subset hUO htrace
  have hu1 : u =ᵐ[volume.restrict U] (fun _ => (1 : ℝ)) := by
    filter_upwards [ht, ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx hxU
  have hs : SobolevPair p U (fun _ => (1 : ℝ)) g :=
    (hu.mono_actual hUO).congr hu1 EventuallyEq.rfl
  exact hs.gradient_ae_unique (sobolevPair_const hu.1 hUb 1) hU

def exteriorSmoothPatch {n : ℕ} (χ φ : Space n → ℝ) : Space n → ℝ :=
  fun x => χ x+(1-χ x)*φ x

theorem smooth_patch_capacity_admissible {n : ℕ} {K U O : Set (Space n)}
    {χ φ : Space n → ℝ} (hχ : SmoothTest U χ) (hφ : SmoothTest O φ)
    (hUO : U ⊆ O) (hχK : ∀ x ∈ K, χ x = 1) :
    BMCompactCapacityV2.Admissible K O (exteriorSmoothPatch χ φ) := by
  have hc : ContDiff ℝ ∞ (exteriorSmoothPatch χ φ) :=
    hχ.1.add ((contDiff_const.sub hχ.1).mul hφ.1)
  have hcompact : HasCompactSupport (exteriorSmoothPatch χ φ) :=
    hχ.2.1.add hφ.2.1.mul_left
  have hs : tsupport (exteriorSmoothPatch χ φ) ⊆ O := by
    change tsupport (χ+(fun x => 1-χ x)*φ) ⊆ O
    exact (tsupport_add _ _).trans (union_subset (hχ.2.2.trans hUO)
      (tsupport_mul_subset_right.trans hφ.2.2))
  refine ⟨hc, hcompact, hs, ?_⟩
  intro x hx
  simp only [exteriorSmoothPatch, hχK x hx, sub_self, zero_mul, add_zero, le_refl]

theorem gradient_exteriorSmoothPatch {n : ℕ} {χ φ : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hφ : ContDiff ℝ ∞ φ) (x : Space n) :
    gradient (exteriorSmoothPatch χ φ) x =
      (1-χ x) • gradient φ x+(1-φ x) • gradient χ x := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hprod : ContDiff ℝ ∞ (fun y => (1-χ y)*φ y) :=
    (contDiff_const.sub hχ).mul hφ
  change gradient (χ+(fun y => (1-χ y)*φ y)) x = _
  rw [gradient_add_smooth_actual hχ hprod]
  simp only [Pi.add_apply]
  have hm := gradient_fun_mul_actual
    (f := fun y => 1-χ y) (h := φ)
    (((differentiable_const (1 : ℝ)).sub hχd) x) (hφd x)
  rw [hm]
  have hs := gradient_fun_sub (differentiable_const (1 : ℝ)) hχd x
  change gradient (fun y => 1-χ y) x = _ at hs
  rw [hs]
  have hz : gradient (fun _ : Space n => (1 : ℝ)) x = 0 := by
    simp only [gradient, fderiv_const_apply, map_zero]
  rw [hz, zero_sub]
  module

private theorem exterior_fixed_multiplier_limit {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {p : ℝ} (hp : 1 < p)
    {f : ℕ → α → E} {g : α → E} {a : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C) (haC : ∀ x, ‖a x‖ ≤ C)
    (hf : ∀ j, MemLp (f j) (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun j => eLpNorm (f j-g) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => a x • (f j x-g x)) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_bounded_smul
    (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)) ENNReal.ofReal_ne_top
    (ENNReal.one_le_ofReal.mpr hp.le) hC (fun _ => ha) ha hf hg
    (fun _ x => haC x) haC (Eventually.of_forall (fun _ => tendsto_const_nhds)) hlim
  simpa only [smul_sub] using h

/- Smooth approximation preserving the actual compact obstacle exactly.
Both convergences follow from the actual W0 graph and an open plateau; they
are not supplied as an approximation premise. -/
set_option maxHeartbeats 1500000 in
theorem exists_capacity_preserving_smooth_approximation {n : ℕ} {p : ℝ}
    {K U O : Set (Space n)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hUO : U ⊆ O) (hOb : Bornology.IsBounded O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g)
    (htrace : ∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) :
    ∃ ψ : ℕ → Space n → ℝ,
      (∀ j, BMCompactCapacityV2.Admissible K O (ψ j)) ∧
      Tendsto (fun j => eLpNorm (ψ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (ψ j) x-g x)
        (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
  have hg0 := hu.1.gradient_ae_zero_on_open_plateau hU (hOb.subset hUO) hUO htrace
  have hg0O : ∀ᵐ x ∂volume.restrict O, x ∈ U → g x = 0 :=
    ae_restrict_of_ae ((ae_restrict_iff' hU.measurableSet).mp hg0)
  obtain ⟨s, hs⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU hKU
  let χ : Space n → ℝ := fun x => Real.smoothTransition (s x)
  have hχ : SmoothTest U χ := ⟨Real.smoothTransition.contDiff.comp hs.1,
    hs.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) s).trans hs.2.2.1⟩
  have hχ0 (x : Space n) : 0 ≤ χ x := Real.smoothTransition.nonneg _
  have hχ1 (x : Space n) : χ x ≤ 1 := Real.smoothTransition.le_one _
  have hχK : ∀ x ∈ K, χ x = 1 :=
    fun x hx => Real.smoothTransition.one_of_one_le (hs.2.2.2 x hx)
  obtain ⟨su, φ, hφ, hfun, hgrad⟩ := hu
  let μ := volume.restrict O
  let q := ENNReal.ofReal p
  let a : Space n → ℝ := fun x => 1-χ x
  let ψ : ℕ → Space n → ℝ := fun j => exteriorSmoothPatch χ (φ j)
  have hψ (j : ℕ) : BMCompactCapacityV2.Admissible K O (ψ j) :=
    smooth_patch_capacity_admissible hχ (hφ j) hUO hχK
  have ha : AEStronglyMeasurable a μ :=
    (continuous_const.sub hχ.1.continuous).aestronglyMeasurable
  have ha1 (x : Space n) : ‖a x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hχ1 x))]
    linarith [hχ0 x]
  have hφu (j : ℕ) : MemLp (φ j) q μ := (hφ j).sobolevPair su.1 |>.2.1
  have hφg (j : ℕ) : MemLp (gradient (φ j)) q μ := (hφ j).sobolevPair su.1 |>.2.2.1
  have hflim := exterior_fixed_multiplier_limit su.1 ha (by norm_num : (0 : ℝ) ≤ 1)
    ha1 hφu su.2.1 hfun
  have hfEq (j : ℕ) : ψ j-u =ᵐ[μ] (fun x => a x • (φ j x-u x)) := by
    filter_upwards [htrace] with x hx
    by_cases hxU : x ∈ U
    · simp only [ψ, exteriorSmoothPatch, Pi.sub_apply, a, hx hxU, smul_eq_mul]
      ring
    · have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxU (hχ.2.2 ht))
      simp only [ψ, exteriorSmoothPatch, Pi.sub_apply, a, hc, sub_zero, one_mul, zero_add, one_smul]
  have hfn (j : ℕ) : eLpNorm (ψ j-u) q μ =
      eLpNorm (fun x => a x • (φ j x-u x)) q μ := eLpNorm_congr_ae (hfEq j)
  have huf : Tendsto (fun j => eLpNorm (ψ j-u) q μ) atTop (𝓝 0) := by
    simpa only [hfn] using hflim
  let A : ℕ → Space n → Space n := fun j x => a x • (gradient (φ j) x-g x)
  let B : ℕ → Space n → Space n := fun j x => (u x-φ j x) • gradient χ x
  have hAlim : Tendsto (fun j => eLpNorm (A j) q μ) atTop (𝓝 0) :=
    exterior_fixed_multiplier_limit su.1 ha (by norm_num : (0 : ℝ) ≤ 1) ha1 hφg su.2.2.1 hgrad
  have hχg := BMCompactCapacityV2.continuous_gradient_of_contDiff hχ.1
  obtain ⟨G0, hG0⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1).exists_bound_of_continuous hχg
  let G : ℝ := max G0 0
  have hG : 0 ≤ G := le_max_right _ _
  have hGx (x : Space n) : ‖gradient χ x‖ ≤ G := (hG0 x).trans (le_max_left _ _)
  have hBbound (j : ℕ) : eLpNorm (B j) q μ ≤ ‖G‖ₑ*eLpNorm (φ j-u) q μ := by
    rw [←eLpNorm_const_smul]
    apply eLpNorm_mono
    intro x
    simp only [B, norm_smul, Pi.smul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hG]
    rw [abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left (hGx x) (abs_nonneg (φ j x-u x))).trans_eq (mul_comm _ _)
  have hBup : Tendsto (fun j => ‖G‖ₑ*eLpNorm (φ j-u) q μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hfun (Or.inr enorm_ne_top)
  have hBlim : Tendsto (fun j => eLpNorm (B j) q μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBup (fun _ => bot_le) hBbound
  have hAm (j : ℕ) : AEStronglyMeasurable (A j) μ := ha.smul ((hφg j).sub su.2.2.1).1
  have hBm (j : ℕ) : AEStronglyMeasurable (B j) μ :=
    (su.2.1.1.sub (hφu j).1).smul hχg.aestronglyMeasurable
  have hgEq (j : ℕ) : (fun x => gradient (ψ j) x-g x) =ᵐ[μ] A j+B j := by
    filter_upwards [htrace, hg0O] with x hx hgx
    rw [gradient_exteriorSmoothPatch hχ.1 (hφ j).1]
    by_cases hxU : x ∈ U
    · simp only [A, B, a, Pi.add_apply, hx hxU, hgx hxU, sub_zero]
    · have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxU (hχ.2.2 ht))
      have hgc : gradient χ x = 0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
        (fun ht => hxU (hχ.2.2 ht))
      simp only [A, B, a, Pi.add_apply, hc, hgc, sub_zero, one_smul, smul_zero, add_zero]
  have hgn (j : ℕ) : eLpNorm (fun x => gradient (ψ j) x-g x) q μ ≤
      eLpNorm (A j) q μ+eLpNorm (B j) q μ := by
    rw [eLpNorm_congr_ae (hgEq j)]
    exact eLpNorm_add_le (hAm j) (hBm j) (ENNReal.one_le_ofReal.mpr su.1.le)
  have hsum : Tendsto (fun j => eLpNorm (A j) q μ+eLpNorm (B j) q μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hAlim.add hBlim
  refine ⟨ψ, hψ, huf, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) hgn

/-- Actual compact relative capacity is bounded by the energy of a genuine
W0 pair with an open unit plateau, without a selected continuity premise. -/
theorem relativeCapacity_le_plateau_energy {n : ℕ} {p : ℝ} {K U O : Set (Space n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hUO : U ⊆ O)
    (hOb : Bornology.IsBounded O) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g)
    (htrace : ∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) :
    BMCompactCapacityV2.relativeCapacity p K O ≤ ENNReal.ofReal (∫ x in O, ‖g x‖^p ∂volume) := by
  have hp0 : 0 < p := zero_lt_one.trans hu.1.1
  obtain ⟨ψ, hψ, -, hgrad⟩ := exists_capacity_preserving_smooth_approximation hK hU hKU hUO hOb hu htrace
  have hψg (j : ℕ) : MemLp (gradient (ψ j)) (ENNReal.ofReal p) (volume.restrict O) :=
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p)
      (hψ j).1 (hψ j).2.1).restrict O
  have hreal := exterior_integral_energy_tendsto_of_Lp hu.1.1 hψg hu.1.2.2.1 hgrad
  have he (j : ℕ) : BMCompactCapacityV2.pEnergy p O (ψ j) =
      ENNReal.ofReal (∫ x in O, ‖gradient (ψ j) x‖^p ∂volume) := by
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_rpow_of_memLp hu.1.1 (hψg j))
      (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))).symm
  have henergy : Tendsto (fun j => BMCompactCapacityV2.pEnergy p O (ψ j)) atTop
      (𝓝 (ENNReal.ofReal (∫ x in O, ‖g x‖^p ∂volume))) := by
    simpa only [Function.comp_def, he] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact le_of_tendsto_of_tendsto tendsto_const_nhds henergy
    (Eventually.of_forall (fun j => BMCompactCapacityV2.relativeCapacity_le_energy p (hψ j)))

end BMCompactPDE
#print axioms BMCompactPDE.exterior_integral_energy_tendsto_of_Lp
#print axioms BMCompactPDE.SobolevPair.gradient_ae_zero_on_open_plateau
#print axioms BMCompactPDE.smooth_patch_capacity_admissible
#print axioms BMCompactPDE.gradient_exteriorSmoothPatch
#print axioms BMCompactPDE.exists_capacity_preserving_smooth_approximation
#print axioms BMCompactPDE.relativeCapacity_le_plateau_energy
