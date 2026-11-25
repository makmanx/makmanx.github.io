import UpstreamGreenLocalStability
import UpstreamGreenLocalGradientBound

/-! Actual homogeneous weak solutions have local gradient stability from
scalar bounds alone. Two nested compact collars supply actual Sobolev data;
actual Caccioppoli derives the needed gradient Lp ceilings. No gradient norm,
gradient closeness, global Sobolev datum, or energy conclusion is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- The local scalar-to-gradient stability coefficient is chosen before both
actual homogeneous weak solutions and all scalar ceilings. In particular an
actual uniformly bounded Green family need not assume a gradient norm bound
in order to use this estimate. -/
theorem exists_local_gradient_stability_of_scalar_bounds
    {n : ℕ} {p : ℝ} (hp : 2≤p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ (u v : Space n → ℝ) (g h : Space n → Space n),
      WeakPHarmonicPair p U u g → WeakPHarmonicPair p U v h →
      ∀ B δ : ℝ,0≤B → 0≤δ → (∀ x∈U,|u x|≤B) →
        (∀ x∈U,|v x|≤B) → (∀ x∈U,|u x-v x|≤δ) →
        Integrable (fun x => ‖g x-h x‖^p) (volume.restrict D) ∧
        (∫ x in D,‖g x-h x‖^p)≤C*δ*B^(p-1) := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hp
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨r,hr,hthick⟩ := hK.exists_cthickening_subset_open hU hD.2.2
  let V : Set (Space n) := thickening r (closure D)
  have hV : LocalDomain V U := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening r (closure D)).trans hthick
  have hDV : LocalDomain D V :=
    ⟨hD.1,hD.2.1,self_subset_thickening hr (closure D)⟩
  have hVU : V⊆U := subset_closure.trans hV.2.2
  obtain ⟨Cs,hCs0,hCs⟩ := exists_local_gradient_stability_constant hp hV.1 hDV
  obtain ⟨Cg,hCg0,hCg⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp1 hU hV
  let C : ℝ := Cs*(2*Cg)^(p-1)
  have hC : 0≤C := mul_nonneg hCs0 (Real.rpow_nonneg (by positivity) _)
  refine ⟨C,hC,?_⟩
  intro u v g h hu hv B δ hB hδ hub hvb hgap
  have hNg := hCg u g hu B hB hub
  have hNh := hCg v h hv B hB hvb
  have huV := hu.source_zero.mono_actual hVU hV.1
  have hvV := hv.source_zero.mono_actual hVU hV.1
  obtain ⟨hI,hE⟩ := hCs 0 u v g h huV hvV (hu.2.2.1 V hV) (hv.2.2.1 V hV)
    δ hδ (fun x hx => hgap x (hVU hx))
  refine ⟨hI,?_⟩
  have hsum : (eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal+
      (eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal≤(2*Cg)*B := by
    linarith only [hNg,hNh]
  have hpownorm := Real.rpow_le_rpow (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    hsum (by linarith : 0≤p-1)
  calc
    (∫ x in D,‖g x-h x‖^p)≤Cs*δ*
        ((eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal+
          (eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal)^(p-1) := hE
    _≤Cs*δ*((2*Cg)*B)^(p-1) :=
      mul_le_mul_of_nonneg_left hpownorm (mul_nonneg hCs0 hδ)
    _=C*δ*B^(p-1) := by
      rw [Real.mul_rpow (mul_nonneg (by norm_num : (0:ℝ)≤2) hCg0) hB]
      dsimp only [C]
      ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_gradient_stability_of_scalar_bounds
