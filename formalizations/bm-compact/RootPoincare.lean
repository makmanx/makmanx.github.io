import BMCompactChecked
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-! Genuine bounded-domain Lp Poincare for the actual W0 graph, 1<p<n.
The smooth inequality is supplied by proved GNS, then both actual graph limits
transfer the estimate. No Poincare premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

theorem exists_smooth_Lp_poincare_constant {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ (ENNReal.ofReal p) (volume.restrict D) ≤
        C*eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D) := by
  let P : ℝ≥0 := p.toNNReal
  have hp0 : 0≤p := (zero_lt_one.trans hp).le
  have hPe : (P : ℝ≥0∞)=ENNReal.ofReal p := rfl
  have hPr : (P : ℝ)=p := by simp [P, Real.toNNReal_of_nonneg hp0]
  let C := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space n)) D P P
  refine ⟨C,?_⟩
  intro φ hφ
  have hs : Function.support φ ⊆ D := (subset_tsupport φ).trans hφ.2.2
  have hgs : Function.support (gradient φ) ⊆ D := by
    intro x hx
    by_contra hxn
    exact hx (BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      (fun h => hxn (hφ.2.2 h)))
  have hP1 : 1≤P := by exact_mod_cast (hPr.symm ▸ hp.le)
  have hPn : P<Module.finrank ℝ (Space n) := by
    apply NNReal.coe_lt_coe.mp
    simpa only [hPr,Space,finrank_euclideanSpace,Fintype.card_fin,NNReal.coe_natCast]
      using hpn
  have he := eLpNorm_le_eLpNorm_fderiv (volume : Measure (Space n))
    (hφ.1.of_le (by simp) : ContDiff ℝ 1 φ) hs hP1 hPn hDb
  have hn : eLpNorm (fderiv ℝ φ) (ENNReal.ofReal p) volume =
      eLpNorm (gradient φ) (ENNReal.ofReal p) volume := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall (fun x => by
      simpa only [gradient] using
        ((toDual ℝ (Space n)).symm.norm_map (fderiv ℝ φ x)).symm)
  rw [hPe,hn] at he
  simpa only [eLpNorm_restrict_eq_of_support_subset hs,
    eLpNorm_restrict_eq_of_support_subset hgs] using he

theorem exists_W0_Lp_poincare_constant {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ {u : Space n → ℝ} {g : Space n → Space n},
      ZeroBoundarySobolevPair p D u g →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict D) ≤
        C*eLpNorm g (ENNReal.ofReal p) (volume.restrict D) := by
  obtain ⟨C,hC⟩ := exists_smooth_Lp_poincare_constant hp hpn hDb
  refine ⟨C,?_⟩
  intro u g hu
  obtain ⟨hs,φ,hφ,huLim,hgLim⟩ := hu
  let q := ENNReal.ofReal p
  let μ := volume.restrict D
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hφm (j : ℕ) := (hφ j).sobolevPair hp
  have hbound (j : ℕ) : eLpNorm u q μ ≤
      eLpNorm (φ j-u) q μ+
        C*(eLpNorm (fun x => gradient (φ j) x-g x) q μ+eLpNorm g q μ) := by
    have ha := eLpNorm_add_le (hs.2.1.sub (hφm j).2.1).1 (hφm j).2.1.1 hq
    rw [sub_add_cancel] at ha
    rw [eLpNorm_sub_comm] at ha
    have hb := eLpNorm_add_le ((hφm j).2.2.1.sub hs.2.2.1).1 hs.2.2.1.1 hq
    rw [sub_add_cancel] at hb
    exact ha.trans (add_le_add le_rfl ((hC _ (hφ j)).trans
      (mul_le_mul_right hb (C : ℝ≥0∞))))
  have hinner := hgLim.add_const (eLpNorm g q μ)
  rw [zero_add] at hinner
  have hmul : Tendsto (fun j => (C : ℝ≥0∞)*(eLpNorm (fun x => gradient (φ j) x-g x) q μ+eLpNorm g q μ))
      atTop (𝓝 ((C : ℝ≥0∞)*eLpNorm g q μ)) :=
    ENNReal.Tendsto.const_mul hinner (Or.inr ENNReal.coe_ne_top)
  have htotal := huLim.add hmul
  rw [zero_add] at htotal
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htotal
    (Eventually.of_forall hbound)

end BMCompactPDE
#print axioms BMCompactPDE.exists_smooth_Lp_poincare_constant
#print axioms BMCompactPDE.exists_W0_Lp_poincare_constant
