import NonlinearAnalyticBatch
import RootAllpEnergyBatch
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Convex

/-! Actual bounded condenser plateau minimizers. The inner constraint is
equality almost everywhere on a prescribed open neighborhood, not a claim of
quasi-everywhere boundary values on an arbitrary thin compact set. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)

def exteriorPlateauClass {n : ℕ} (U O : Set (Space n)) :
    Set (w0LpGraph p hp n O) :=
  {w | ∀ᵐ x ∂volume.restrict O, x ∈ U → (w.1.1 : Space n → ℝ) x = 1}

theorem isClosed_exteriorPlateauClass {n : ℕ} (U O : Set (Space n)) :
    IsClosed (exteriorPlateauClass p hp U O) := by
  apply IsSeqClosed.isClosed
  intro w z hw hz
  have hs : Tendsto (fun j : ℕ => (w j).1.1) atTop (𝓝 z.1.1) :=
    (continuous_fst.tendsto z.1).comp ((continuous_subtype_val.tendsto z).comp hz)
  obtain ⟨σ, -, hσ⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  change ∀ j, ∀ᵐ x ∂volume.restrict O, x ∈ U → (w j).1.1 x = 1 at hw
  change ∀ᵐ x ∂volume.restrict O, x ∈ U → z.1.1 x = 1
  filter_upwards [ae_all_iff.2 hw, hσ] with x hx hl
  intro hxU
  have he : (fun j : ℕ => (w (σ j)).1.1 x) = (fun _ => (1 : ℝ)) :=
    funext (fun j => hx (σ j) hxU)
  rw [he] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

theorem convex_exteriorPlateauClass {n : ℕ} (U O : Set (Space n)) :
    Convex ℝ (exteriorPlateauClass p hp U O) := by
  intro x hx y hy a b ha hb hab
  change ∀ᵐ z ∂volume.restrict O, z ∈ U →
    ((a • x.1.1 + b • y.1.1 : ScalarLp p n O) : Space n → ℝ) z = 1
  filter_upwards [hx, hy, Lp.coeFn_add (a • x.1.1) (b • y.1.1),
    Lp.coeFn_smul a x.1.1, Lp.coeFn_smul b y.1.1] with z hx hy hadd hax hby
  intro hz
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hax, hby]
  simp only [Pi.smul_apply, smul_eq_mul, hx hz, hy hz, mul_one]
  exact hab

theorem exteriorPlateauClass_nonempty_of_smooth {n : ℕ} {U O : Set (Space n)}
    {η : Space n → ℝ} (hη : SmoothTest O η)
    (hηU : ∀ x ∈ U, η x = 1) :
    (exteriorPlateauClass p hp U O).Nonempty := by
  obtain ⟨z, hzu, -⟩ := (hη.zeroBoundarySobolevPair hp).exists_w0LpGraph_representatives hp
  refine ⟨z, ?_⟩
  filter_upwards [hzu] with x hx
  intro hxU
  exact hx.trans (hηU x hxU)

theorem exteriorPlateauClass_nonempty {n : ℕ} {U O : Set (Space n)}
    (hO : IsOpen O) (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    (exteriorPlateauClass p hp U O).Nonempty := by
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hUc hO hUO
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest O η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1⟩
  exact exteriorPlateauClass_nonempty_of_smooth p hp hη
    (fun x hx => Real.smoothTransition.one_of_one_le (hf.2.2.2 x (subset_closure hx)))

set_option maxHeartbeats 1000000 in
theorem exists_exteriorPlateauClass_minimum {n : ℕ} (hpn : p < (n : ℝ))
    {U O : Set (Space n)} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ v ∈ exteriorPlateauClass p hp U O,
      ∀ z ∈ exteriorPlateauClass p hp U O, ‖v.1.2‖^p ≤ ‖z.1.2‖^p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  letI : CompleteSpace (w0LpGraph p hp n O) :=
    (isClosed_w0LpGraph p hp n O).completeSpace_coe
  let J : w0LpGraph p hp n O → ℝ := fun w => ‖w.1.2‖^p
  obtain ⟨A, hA⟩ := exists_w0LpGradient_antilipschitz p hp hpn hOb
  let C : ℝ := (A : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hinv (w : w0LpGraph p hp n O) : ‖w‖ ≤ C*‖w.1.2‖ := by
    have hh : ‖w‖ ≤ (A : ℝ)*‖w.1.2‖ := by
      simpa only [dist_eq_norm, map_zero, sub_zero, w0LpGradient_apply] using hA.le_mul_dist w 0
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hcont : Continuous J :=
    (w0LpGradient p hp n O).continuous.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hbdd : BddBelow (J '' exteriorPlateauClass p hp U O) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ,
      ∀ w ∈ exteriorPlateauClass p hp U O, J w ≤ a → ‖w‖ ≤ R := by
    intro a
    refine ⟨C*(a+1), ?_⟩
    intro w _ hw
    have hpow : ‖w.1.2‖ ≤ ‖w.1.2‖^p + 1 := by
      by_cases ht : ‖w.1.2‖ ≤ 1
      · linarith [Real.rpow_nonneg (norm_nonneg w.1.2) p]
      · have hh := Real.self_le_rpow_of_one_le (le_of_not_ge ht) hp.le
        linarith
    exact (hinv w).trans (mul_le_mul_of_nonneg_left (by dsimp [J] at hw; linarith) hC.le)
  have hgap : ∀ R ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧
      ∀ x ∈ exteriorPlateauClass p hp U O, ∀ y ∈ exteriorPlateauClass p hp U O,
        ‖x‖ ≤ R → ‖y‖ ≤ R → ε ≤ ‖x-y‖ →
        J ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤ (J x+J y)/2-κ := by
    intro R ε hε
    obtain ⟨κ, hκ, hfield⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := volume.restrict O) hp R (ε/C) (div_pos hε hC)
    refine ⟨κ, hκ, ?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖ ≤ (A : ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm, w0LpGradient_apply] using hA.le_mul_dist x y
    have he : ε ≤ C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hsep : ε/C ≤ ‖x.1.2-y.1.2‖ :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖x.1.2‖ ≤ R := (le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx
    have hFy : ‖y.1.2‖ ≤ R := (le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy
    have hh := hfield x.1.2 y.1.2 hFx hFy hsep
    have hm : ((1/2 : ℝ) • x + (1/2 : ℝ) • y).1.2 =
        (1/2 : ℝ) • (x.1.2+y.1.2) := by
      change (1/2 : ℝ) • x.1.2 + (1/2 : ℝ) • y.1.2 = _
      rw [smul_add]
    dsimp only [J]
    rw [hm]
    linarith
  exact BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
    (exteriorPlateauClass_nonempty p hp hO hUc hUO)
    (isClosed_exteriorPlateauClass p hp U O) (convex_exteriorPlateauClass p hp U O)
    hcont.continuousOn hbdd hcoercive hgap

/-- A genuine bounded Sobolev condenser minimum with an inner plateau.
Neither an admissible weak minimizer nor compactness/existence is assumed. -/
theorem exists_bounded_plateau_energy_minimum {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) {U O : Set (Space n)}
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      (∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p O v h →
        (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
        (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨w, hw, hmin⟩ := exists_exteriorPlateauClass_minimum p hp hpn hO hOb hUc hUO
  refine ⟨w.1.1, w.1.2, w.2, hw, ?_⟩
  intro v h hv hvU
  obtain ⟨z, hzu, hzg⟩ := hv.exists_w0LpGraph_representatives hp
  have hz : z ∈ exteriorPlateauClass p hp U O := by
    filter_upwards [hzu, hvU] with x hx hy
    intro hxU
    exact hx.trans (hy hxU)
  have hh := hmin z hz
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp),
    BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at hh
  have he : (∫ x in O, ‖(z.1.2 : Space n → Space n) x‖^p) =
      ∫ x in O, ‖h x‖^p := integral_congr_ae (hzg.fun_comp (fun a => ‖a‖^p))
  exact hh.trans_eq he

end BMCompactPDE
#print axioms BMCompactPDE.isClosed_exteriorPlateauClass
#print axioms BMCompactPDE.convex_exteriorPlateauClass
#print axioms BMCompactPDE.exteriorPlateauClass_nonempty_of_smooth
#print axioms BMCompactPDE.exteriorPlateauClass_nonempty
#print axioms BMCompactPDE.exists_exteriorPlateauClass_minimum
#print axioms BMCompactPDE.exists_bounded_plateau_energy_minimum
