import NonlinearW0Graph
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import ExteriorPlateauMin
import PotentialSobolevBoost

/-! Exact exterior construction batch; readable segments add zero extra counts. -/
section ExteriorSegment_ExteriorZeroExtension

/-! Genuine zero extension of the actual two-component W0 graph. Smooth
approximants vanish off the smaller domain, so both actual Lp limits extend;
the distributional gradient of the extension is proved by graph closure. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem ZeroBoundarySobolevPair.zeroExtend_to_superset {n : ℕ} {p : ℝ}
    {D O : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hD : MeasurableSet D) (hDO : D ⊆ O) :
    ZeroBoundarySobolevPair p O (D.indicator u) (D.indicator g) := by
  obtain ⟨hs, φ, hφ, hfun, hgrad⟩ := hu
  have hμ : (volume.restrict O).restrict D = volume.restrict D :=
    Measure.restrict_restrict_of_subset hDO
  have huM : MemLp (D.indicator u) (ENNReal.ofReal p) (volume.restrict O) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hμ]
    exact hs.2.1
  have hgM : MemLp (D.indicator g) (ENNReal.ofReal p) (volume.restrict O) := by
    apply (memLp_indicator_iff_restrict hD).mpr
    rw [hμ]
    exact hs.2.2.1
  have hφO (j : ℕ) : SmoothTest O (φ j) :=
    ⟨(hφ j).1, (hφ j).2.1, (hφ j).2.2.trans hDO⟩
  have hφ0 (j : ℕ) (x : Space n) (hx : x ∉ D) : φ j x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx ((hφ j).2.2 ht))
  have hgrad0 (j : ℕ) (x : Space n) (hx : x ∉ D) : gradient (φ j) x = 0 :=
    BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun ht => hx ((hφ j).2.2 ht))
  have hfe (j : ℕ) : φ j-D.indicator u = D.indicator (φ j-u) := by
    funext x
    by_cases hx : x ∈ D
    · simp only [Pi.sub_apply, indicator_of_mem hx]
    · simp only [Pi.sub_apply, indicator_of_notMem hx, hφ0 j x hx, sub_zero]
  have hge (j : ℕ) : (fun x => gradient (φ j) x-D.indicator g x) =
      D.indicator (fun x => gradient (φ j) x-g x) := by
    funext x
    by_cases hx : x ∈ D
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, hgrad0 j x hx, sub_zero]
  have hfn (j : ℕ) :
      eLpNorm (φ j-D.indicator u) (ENNReal.ofReal p) (volume.restrict O) =
        eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict D) := by
    rw [hfe, eLpNorm_indicator_eq_eLpNorm_restrict hD, hμ]
  have hgn (j : ℕ) :
      eLpNorm (fun x => gradient (φ j) x-D.indicator g x) (ENNReal.ofReal p)
        (volume.restrict O) =
        eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict D) := by
    rw [hge, eLpNorm_indicator_eq_eLpNorm_restrict hD, hμ]
  exact zeroBoundarySobolevPair_of_eLpNorm_limits hs.1
    (fun j => (hφO j).zeroBoundarySobolevPair hs.1) huM hgM
    (by simpa only [hfn] using hfun) (by simpa only [hgn] using hgrad)

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorZeroExtension

section ExteriorSegment_ExteriorPlateauHarmonic

/-! The constructed bounded plateau minimizer satisfies the actual weak
p-Laplace equation off the closed inner neighborhood. No weak equation or
classical regularity of the minimizer is supplied as an existence premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem plateau_minimum_smooth_equation {n : ℕ} {p : ℝ} {U O : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g)
    (huU : ∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1)
    (hmin : ∀ (v : Space n → ℝ) (h : Space n → Space n),
      ZeroBoundarySobolevPair p O v h →
      (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
      (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p)
    {φ : Space n → ℝ} (hφ : SmoothTest (O \ closure U) φ) :
    (∫ x in O, fluxPairing p g (gradient φ) x) = 0 := by
  have hp : 1 < p := hu.1.1
  have hφO : SmoothTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans diff_subset⟩
  have hφW := hφO.zeroBoundarySobolevPair hp
  have hφ0 (x : Space n) (hx : x ∈ U) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => (hφ.2.2 ht).2 (subset_closure hx))
  let F : ℝ → ℝ := fun t => ∫ x in O, ‖g x+t • gradient φ x‖^p
  have hlocal : IsLocalMin F 0 := by
    apply Eventually.of_forall
    intro t
    have hw : ZeroBoundarySobolevPair p O (u+t • φ) (g+t • gradient φ) :=
      hu.add_actual (hφW.smul_actual t)
    have ht : ∀ᵐ x ∂volume.restrict O, x ∈ U → (u+t • φ) x = 1 := by
      filter_upwards [huU] with x hx
      intro hxU
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hφ0 x hxU, mul_zero,
        add_zero, hx hxU]
    have hh := hmin (u+t • φ) (g+t • gradient φ) hw ht
    simpa only [F, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero] using hh
  have hd : HasDerivAt F (p*(∫ x in O, inner ℝ (pFlux p (g x)) (gradient φ x))) 0 := by
    convert! hasDerivAt_integral_energy_line hp hu.1.2.2.1 hφW.1.2.2.1 using 1 <;>
      simp only [F]
  have hz := hlocal.hasDerivAt_eq_zero hd
  change p*(∫ x in O, fluxPairing p g (gradient φ) x) = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (zero_lt_one.trans hp).ne'

theorem plateau_minimum_weakPHarmonic_off_closure {n : ℕ} {p : ℝ}
    {U O : Set (Space n)} (hO : IsOpen O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p O u g)
    (huU : ∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1)
    (hmin : ∀ (v : Space n → ℝ) (h : Space n → Space n),
      ZeroBoundarySobolevPair p O v h →
      (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
      (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p) :
    WeakPHarmonicPair p (O \ closure U) u g := by
  have hD : IsOpen (O \ closure U) := hO.sdiff isClosed_closure
  have he : ∀ φ : Space n → ℝ, SmoothTest (O \ closure U) φ →
      (∫ x in O \ closure U, fluxPairing p g (gradient φ) x) =
        (0 : ℝ)*(∫ x in O \ closure U, φ x) := by
    intro φ hφ
    have hzero (x : Space n) (hx : x ∉ O \ closure U) :
        fluxPairing p g (gradient φ) x = 0 := by
      have hg : gradient φ x = 0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
        (fun ht => hx (hφ.2.2 ht))
      simp only [fluxPairing, hg, inner_zero_right]
    have hIntD : (∫ x in O \ closure U, fluxPairing p g (gradient φ) x) =
        ∫ x, fluxPairing p g (gradient φ) x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have hIntO : (∫ x in O, fluxPairing p g (gradient φ) x) =
        ∫ x, fluxPairing p g (gradient φ) x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzero x (fun hd => hx hd.1))
    rw [hIntD, ←hIntO, plateau_minimum_smooth_equation hu huU hmin hφ, zero_mul]
  exact (weakPSourcePair_of_sobolev_smooth_source_equation hD
    (hu.1.mono_actual diff_subset) he).harmonic_of_source_zero

/-- The bounded condenser object is constructed, including its actual weak
equation on the exterior region inside the outer domain. -/
theorem exists_bounded_plateau_harmonic_minimum {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) {U O : Set (Space n)}
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      (∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) ∧
      WeakPHarmonicPair p (O \ closure U) u g ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p O v h →
        (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
        (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p := by
  obtain ⟨u, g, hu, huU, hm⟩ := exists_bounded_plateau_energy_minimum hp hpn hO hOb hUc hUO
  exact ⟨u, g, hu, huU, plateau_minimum_weakPHarmonic_off_closure hO hu huU hm, hm⟩

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorPlateauHarmonic

section ExteriorSegment_ExteriorEnergyFamily

/-! A genuinely constructed family of bounded condenser solutions with a
fixed-cutoff global energy bound. Exhaustion and passage to an exterior limit
are further steps; existence of this family is not a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1000000 in
theorem exists_uniform_energy_plateau_family {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) {U : Set (Space n)}
    (hUc : IsCompact (closure U)) (O : ℕ → Set (Space n))
    (hO : ∀ j, IsOpen (O j)) (hOb : ∀ j, Bornology.IsBounded (O j))
    (hUO : ∀ j, closure U ⊆ O j) {η : Space n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηO : ∀ j, tsupport η ⊆ O j) (hηU : ∀ x ∈ U, η x = 1) :
    ∃ u : ℕ → Space n → ℝ, ∃ g : ℕ → Space n → Space n,
      Integrable (fun x => ‖gradient η x‖^p) volume ∧
      ∀ j, ZeroBoundarySobolevPair p univ (u j) (g j) ∧
        (∀ᵐ x ∂volume, x ∈ U → u j x = 1) ∧
        WeakPHarmonicPair p (O j \ closure U) (u j) (g j) ∧
        (∫ x, ‖g j x‖^p) ≤ ∫ x, ‖gradient η x‖^p ∧
        MemLp (u j) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
        eLpNorm (u j) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ≤
          eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
            eLpNorm (g j) (ENNReal.ofReal p) volume := by
  have hex (j : ℕ) := exists_bounded_plateau_harmonic_minimum hp hpn
    (hO j) (hOb j) hUc (hUO j)
  choose v h hv hvU hh hm using hex
  let u : ℕ → Space n → ℝ := fun j => (O j).indicator (v j)
  let g : ℕ → Space n → Space n := fun j => (O j).indicator (h j)
  have hηI : Integrable (fun x => ‖gradient η x‖^p) volume :=
    integrable_norm_rpow_of_memLp hp
      (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hη hηc)
  refine ⟨u, g, hηI, ?_⟩
  intro j
  have hw : ZeroBoundarySobolevPair p univ (u j) (g j) :=
    (hv j).zeroExtend_to_superset (hO j).measurableSet (subset_univ _)
  have htrace : ∀ᵐ x ∂volume, x ∈ U → u j x = 1 := by
    have ht := (ae_restrict_iff' (hO j).measurableSet).mp (hvU j)
    filter_upwards [ht] with x hx
    intro hxU
    have hxO : x ∈ O j := hUO j (subset_closure hxU)
    change (O j).indicator (v j) x = 1
    rw [indicator_of_mem hxO]
    exact hx hxO hxU
  have hvEq : v j =ᵐ[volume.restrict (O j \ closure U)] u j := by
    filter_upwards [ae_restrict_mem ((hO j).sdiff isClosed_closure).measurableSet] with x hx
    exact (indicator_of_mem hx.1 (v j)).symm
  have hgEq : h j =ᵐ[volume.restrict (O j \ closure U)] g j := by
    filter_upwards [ae_restrict_mem ((hO j).sdiff isClosed_closure).measurableSet] with x hx
    exact (indicator_of_mem hx.1 (h j)).symm
  have hH : WeakPHarmonicPair p (O j \ closure U) (u j) (g j) :=
    (hh j).congr_ae hvEq hgEq
  have hE : (∫ x, ‖g j x‖^p) ≤ ∫ x, ‖gradient η x‖^p := by
    have hηW : ZeroBoundarySobolevPair p (O j) η (gradient η) :=
      (show SmoothTest (O j) η from ⟨hη, hηc, hηO j⟩).zeroBoundarySobolevPair hp
    have hmin := hm j η (gradient η) hηW (Eventually.of_forall hηU)
    have he : (fun x => ‖g j x‖^p) = (O j).indicator (fun x => ‖h j x‖^p) := by
      funext x
      by_cases hx : x ∈ O j
      · simp only [g, indicator_of_mem hx]
      · simp only [g, indicator_of_notMem hx, norm_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
    have hη0 (x : Space n) (hx : x ∉ O j) : ‖gradient η x‖^p = 0 := by
      rw [BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hηO j ht)),
        norm_zero, Real.zero_rpow (zero_lt_one.trans hp).ne']
    rw [he, integral_indicator (hO j).measurableSet]
    exact hmin.trans_eq (setIntegral_eq_integral_of_forall_compl_eq_zero hη0)
  have hs := hw.critical_sobolev_explicit hpn
  refine ⟨hw, htrace, hH, hE, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using hs.1
  · simpa only [Measure.restrict_univ] using hs.2

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorEnergyFamily

#print axioms BMCompactPDE.ZeroBoundarySobolevPair.zeroExtend_to_superset
#print axioms BMCompactPDE.plateau_minimum_smooth_equation
#print axioms BMCompactPDE.plateau_minimum_weakPHarmonic_off_closure
#print axioms BMCompactPDE.exists_bounded_plateau_harmonic_minimum
#print axioms BMCompactPDE.exists_uniform_energy_plateau_family
