import ExteriorCondenserConstruction
import PotentialSobolevBoost
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Sequences
import RootMixedLpClosure

/-! Exact global exterior construction batch; readable segments add zero extra counts. -/
section ExteriorSegment_ExteriorHomogeneousGraph

/-! The homogeneous energy graph is a concrete closed submodule of actual
Lq scalar functions and Lp vector fields. It is the closure of genuine smooth
compact pairs, not an assumed class of potentials or an abstract gradient-only
completion. Local Sobolev identification is a separate proved bridge. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

abbrev ExteriorScalarLp (q : ℝ) (n : ℕ) := Lp ℝ (ENNReal.ofReal q) (volume : Measure (Space n))
abbrev ExteriorVectorLp (p : ℝ) (n : ℕ) := Lp (Space n) (ENNReal.ofReal p) (volume : Measure (Space n))

variable (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

def exteriorSmoothGraph (n : ℕ) : Submodule ℝ (ExteriorScalarLp q n × ExteriorVectorLp p n) where
  carrier := {z | ∃ φ : Space n → ℝ, SmoothTest univ φ ∧
    (z.1 : Space n → ℝ) =ᵐ[volume] φ ∧
    (z.2 : Space n → Space n) =ᵐ[volume] gradient φ}
  zero_mem' := by
    refine ⟨0, ⟨contDiff_const, ?_, subset_univ _⟩, Lp.coeFn_zero ℝ (ENNReal.ofReal q) volume, ?_⟩
    · simp [HasCompactSupport]
    · filter_upwards [Lp.coeFn_zero (Space n) (ENNReal.ofReal p) volume] with x hx
      change ((0 : ExteriorVectorLp p n) : Space n → Space n) x = gradient 0 x
      rw [hx]
      change (0 : Space n) = gradient (fun _ : Space n => (0 : ℝ)) x
      simp only [gradient_fun_const]
  add_mem' := by
    rintro z w ⟨φ, hφ, hzφ, hzg⟩ ⟨ψ, hψ, hwψ, hwg⟩
    refine ⟨φ+ψ, ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, subset_univ _⟩, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add z.1 w.1, hzφ, hwψ] with x hadd hz hw
      change ((z.1+w.1 : ExteriorScalarLp q n) : Space n → ℝ) x = _
      rw [hadd]
      simp only [Pi.add_apply, hz, hw]
    · filter_upwards [Lp.coeFn_add z.2 w.2, hzg, hwg] with x hadd hz hw
      change ((z.2+w.2 : ExteriorVectorLp p n) : Space n → Space n) x = _
      rw [hadd]
      simp only [Pi.add_apply, hz, hw]
      exact (congr_fun (gradient_add_smooth_actual hφ.1 hψ.1) x).symm
  smul_mem' := by
    rintro c z ⟨φ, hφ, hzφ, hzg⟩
    have hc : SmoothTest univ (c • φ) := ⟨hφ.1.const_smul c,
      hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport (c • φ))
        (tsupport_smul_subset_right (fun _ : Space n => c) φ), subset_univ _⟩
    refine ⟨c • φ, hc, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul c z.1, hzφ] with x hc hz
      change ((c • z.1 : ExteriorScalarLp q n) : Space n → ℝ) x = _
      rw [hc]
      simp only [Pi.smul_apply, hz]
    · filter_upwards [Lp.coeFn_smul c z.2, hzg] with x hc hz
      change ((c • z.2 : ExteriorVectorLp p n) : Space n → Space n) x = _
      rw [hc]
      simp only [Pi.smul_apply, hz]
      exact (congr_fun (gradient_smul_smooth_actual hφ.1 c) x).symm

def exteriorHomogeneousGraph (n : ℕ) : Submodule ℝ (ExteriorScalarLp q n × ExteriorVectorLp p n) :=
  (exteriorSmoothGraph p q n).topologicalClosure

theorem isClosed_exteriorHomogeneousGraph (n : ℕ) :
    IsClosed (exteriorHomogeneousGraph p q n : Set (ExteriorScalarLp q n × ExteriorVectorLp p n)) :=
  (exteriorSmoothGraph p q n).isClosed_topologicalClosure

theorem exteriorHomogeneousGraph_scalar_bound {n : ℕ} (hp : 1 < p) (hpn : p < (n : ℝ))
    (hq : q = (n : ℝ)*p/((n : ℝ)-p)) (w : exteriorHomogeneousGraph p q n) :
    ‖w.1.1‖ ≤ (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ)*‖w.1.2‖ := by
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p
  let T : Set (ExteriorScalarLp q n × ExteriorVectorLp p n) := {z | ‖z.1‖ ≤ (S : ℝ)*‖z.2‖}
  have hT : IsClosed T := isClosed_le continuous_fst.norm (continuous_snd.norm.const_mul (S : ℝ))
  have hs : (exteriorSmoothGraph p q n : Set (ExteriorScalarLp q n × ExteriorVectorLp p n)) ⊆ T := by
    rintro z ⟨φ, hφ, hzu, hzg⟩
    have hG := ((hφ.zeroBoundarySobolevPair hp).critical_sobolev_explicit hpn).2
    have hGN : eLpNorm (z.1 : Space n → ℝ) (ENNReal.ofReal q) volume ≤
        S*eLpNorm (z.2 : Space n → Space n) (ENNReal.ofReal p) volume := by
      rw [eLpNorm_congr_ae hzu, eLpNorm_congr_ae hzg]
      simpa only [hq, Measure.restrict_univ, S] using hG
    have hfin : (S : ℝ≥0∞)*eLpNorm (z.2 : Space n → Space n) (ENNReal.ofReal p) volume ≠ (∞ : ℝ≥0∞) :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top z.2)
    have hr := ENNReal.toReal_mono hfin hGN
    simpa only [T, mem_setOf_eq, Lp.norm_def, ENNReal.toReal_mul, ENNReal.coe_toReal] using hr
  have hw : w.1 ∈ closure (exteriorSmoothGraph p q n : Set (ExteriorScalarLp q n × ExteriorVectorLp p n)) := w.2
  simpa only [T, S, mem_setOf_eq] using (closure_minimal hs hT) hw

def exteriorHomogeneousGradient (n : ℕ) :
    exteriorHomogeneousGraph p q n →L[ℝ] ExteriorVectorLp p n :=
  (ContinuousLinearMap.snd ℝ (ExteriorScalarLp q n) (ExteriorVectorLp p n)).comp
    (exteriorHomogeneousGraph p q n).subtypeL

theorem exists_exteriorHomogeneousGradient_antilipschitz {n : ℕ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) (hq : q = (n : ℝ)*p/((n : ℝ)-p)) :
    ∃ C : ℝ≥0, AntilipschitzWith C (exteriorHomogeneousGradient p q n) := by
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p
  let C : ℝ≥0 := max S 1
  have hSC : (S : ℝ) ≤ (C : ℝ) := by exact_mod_cast le_max_left S 1
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast le_max_right S 1
  refine ⟨C, (exteriorHomogeneousGradient p q n).antilipschitz_of_bound ?_⟩
  intro w
  change max ‖w.1.1‖ ‖w.1.2‖ ≤ (C : ℝ)*‖w.1.2‖
  exact max_le ((exteriorHomogeneousGraph_scalar_bound p q hp hpn hq w).trans
    (mul_le_mul_of_nonneg_right hSC (norm_nonneg _)))
    (le_mul_of_one_le_left (norm_nonneg _) hC1)

theorem exteriorHomogeneousGraph_smooth_approximation {n : ℕ}
    (w : exteriorHomogeneousGraph p q n) :
    ∃ φ : ℕ → Space n → ℝ, (∀ j, SmoothTest univ (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume) atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hw : w.1 ∈ closure (exteriorSmoothGraph p q n : Set (ExteriorScalarLp q n × ExteriorVectorLp p n)) := w.2
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose φ hφ hzu hzg using hz
  have h1 := (continuous_fst.tendsto w.1).comp hlim
  have h2 := (continuous_snd.tendsto w.1).comp hlim
  have hl1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).1) w.1.1).mp h1
  have hl2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).2) w.1.2).mp h2
  refine ⟨φ, hφ, ?_, ?_⟩
  · have he (j : ℕ) : eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume =
        eLpNorm (((z j).1 : Space n → ℝ)-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae ((hzu j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl1
  · have he (j : ℕ) : eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) volume =
        eLpNorm (((z j).2 : Space n → Space n)-(w.1.2 : Space n → Space n)) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae ((hzg j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl2

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorHomogeneousGraph

section ExteriorSegment_ExteriorGlobalMinimum

/-! A global finite-energy minimum in the concrete Lp* scalar/Lp gradient
completion of genuine smooth compact pairs. No exterior solution, minimizing
sequence, compactness or energy-convergence conclusion is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

variable (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

def exteriorGlobalPlateauClass {n : ℕ} (U : Set (Space n)) :
    Set (exteriorHomogeneousGraph p q n) :=
  {w | ∀ᵐ x ∂volume, x ∈ U → (w.1.1 : Space n → ℝ) x = 1}

theorem isClosed_exteriorGlobalPlateauClass {n : ℕ} (U : Set (Space n)) :
    IsClosed (exteriorGlobalPlateauClass p q U) := by
  apply IsSeqClosed.isClosed
  intro w z hw hz
  have hs : Tendsto (fun j : ℕ => (w j).1.1) atTop (𝓝 z.1.1) :=
    (continuous_fst.tendsto z.1).comp ((continuous_subtype_val.tendsto z).comp hz)
  obtain ⟨σ, -, hσ⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  change ∀ j, ∀ᵐ x ∂volume, x ∈ U → (w j).1.1 x = 1 at hw
  change ∀ᵐ x ∂volume, x ∈ U → z.1.1 x = 1
  filter_upwards [ae_all_iff.2 hw, hσ] with x hx hl
  intro hxU
  have he : (fun j : ℕ => (w (σ j)).1.1 x) = (fun _ => (1 : ℝ)) :=
    funext (fun j => hx (σ j) hxU)
  rw [he] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

theorem convex_exteriorGlobalPlateauClass {n : ℕ} (U : Set (Space n)) :
    Convex ℝ (exteriorGlobalPlateauClass p q U) := by
  intro x hx y hy a b ha hb hab
  change ∀ᵐ z ∂volume, z ∈ U →
    ((a • x.1.1 + b • y.1.1 : ExteriorScalarLp q n) : Space n → ℝ) z = 1
  filter_upwards [hx, hy, Lp.coeFn_add (a • x.1.1) (b • y.1.1),
    Lp.coeFn_smul a x.1.1, Lp.coeFn_smul b y.1.1] with z hx hy hadd hax hby
  intro hz
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hax, hby]
  simp only [Pi.smul_apply, smul_eq_mul, hx hz, hy hz, mul_one]
  exact hab

theorem exteriorGlobalPlateauClass_nonempty {n : ℕ} {U : Set (Space n)}
    (hUc : IsCompact (closure U)) : (exteriorGlobalPlateauClass p q U).Nonempty := by
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hUc isOpen_univ (subset_univ _)
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest univ η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))), subset_univ _⟩
  have hu : MemLp η (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) hη.1 hη.2.1
  have hg : MemLp (gradient η) (ENNReal.ofReal p) volume :=
    BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hη.1 hη.2.1
  let z : ExteriorScalarLp q n × ExteriorVectorLp p n := (hu.toLp η, hg.toLp (gradient η))
  have hz : z ∈ exteriorSmoothGraph p q n :=
    ⟨η, hη, MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hg⟩
  let w : exteriorHomogeneousGraph p q n :=
    ⟨z, (exteriorSmoothGraph p q n).le_topologicalClosure hz⟩
  refine ⟨w, ?_⟩
  filter_upwards [MemLp.coeFn_toLp hu] with x hx
  intro hxU
  exact hx.trans (Real.smoothTransition.one_of_one_le (hf.2.2.2 x (subset_closure hxU)))

set_option maxHeartbeats 1000000 in
theorem exists_exteriorGlobalPlateauClass_minimum {n : ℕ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) (hq : q = (n : ℝ)*p/((n : ℝ)-p))
    {U : Set (Space n)} (hUc : IsCompact (closure U)) :
    ∃ v ∈ exteriorGlobalPlateauClass p q U,
      ∀ z ∈ exteriorGlobalPlateauClass p q U, ‖v.1.2‖^p ≤ ‖z.1.2‖^p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  letI : CompleteSpace (exteriorHomogeneousGraph p q n) :=
    (isClosed_exteriorHomogeneousGraph p q n).completeSpace_coe
  let J : exteriorHomogeneousGraph p q n → ℝ := fun w => ‖w.1.2‖^p
  obtain ⟨A, hA⟩ := exists_exteriorHomogeneousGradient_antilipschitz p q hp hpn hq
  have hproj (w : exteriorHomogeneousGraph p q n) :
      exteriorHomogeneousGradient p q n w = w.1.2 := rfl
  have hproj0 : (0 : exteriorHomogeneousGraph p q n).1.2 =
      (0 : ExteriorVectorLp p n) := rfl
  let C : ℝ := (A : ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hinv (w : exteriorHomogeneousGraph p q n) : ‖w‖ ≤ C*‖w.1.2‖ := by
    have hh : ‖w‖ ≤ (A : ℝ)*‖w.1.2‖ := by
      simpa only [dist_eq_norm, hproj, hproj0, sub_zero] using hA.le_mul_dist w 0
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hcont : Continuous J :=
    (exteriorHomogeneousGradient p q n).continuous.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hbdd : BddBelow (J '' exteriorGlobalPlateauClass p q U) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ,
      ∀ w ∈ exteriorGlobalPlateauClass p q U, J w ≤ a → ‖w‖ ≤ R := by
    intro a
    refine ⟨C*(a+1), ?_⟩
    intro w _ hw
    have hpow : ‖w.1.2‖ ≤ ‖w.1.2‖^p+1 := by
      by_cases ht : ‖w.1.2‖ ≤ 1
      · linarith [Real.rpow_nonneg (norm_nonneg w.1.2) p]
      · have hh := Real.self_le_rpow_of_one_le (le_of_not_ge ht) hp.le
        linarith
    exact (hinv w).trans (mul_le_mul_of_nonneg_left (by dsimp [J] at hw; linarith) hC.le)
  have hgap : ∀ R ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧
      ∀ x ∈ exteriorGlobalPlateauClass p q U, ∀ y ∈ exteriorGlobalPlateauClass p q U,
        ‖x‖ ≤ R → ‖y‖ ≤ R → ε ≤ ‖x-y‖ →
        J ((1/2 : ℝ) • x+(1/2 : ℝ) • y) ≤ (J x+J y)/2-κ := by
    intro R ε hε
    obtain ⟨κ, hκ, hfield⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := (volume : Measure (Space n))) hp R (ε/C) (div_pos hε hC)
    refine ⟨κ, hκ, ?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖ ≤ (A : ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm, hproj] using hA.le_mul_dist x y
    have he : ε ≤ C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hsep : ε/C ≤ ‖x.1.2-y.1.2‖ :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖x.1.2‖ ≤ R := (le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx
    have hFy : ‖y.1.2‖ ≤ R := (le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy
    have hh := hfield x.1.2 y.1.2 hFx hFy hsep
    have hm : ((1/2 : ℝ) • x+(1/2 : ℝ) • y).1.2 =
        (1/2 : ℝ) • (x.1.2+y.1.2) := by
      change (1/2 : ℝ) • x.1.2+(1/2 : ℝ) • y.1.2 = _
      rw [smul_add]
    dsimp only [J]
    rw [hm]
    linarith
  exact BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
    (exteriorGlobalPlateauClass_nonempty p q hUc)
    (isClosed_exteriorGlobalPlateauClass p q U) (convex_exteriorGlobalPlateauClass p q U)
    hcont.continuousOn hbdd hcoercive hgap

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorGlobalMinimum

section ExteriorSegment_ExteriorGlobalPotential

/-! A genuine global finite-energy exterior weak solution on the complement
of a compact inner neighborhood. The scalar belongs to Lp*, the vector field
to Lp, and actual local weak gradients are obtained from mixed-norm closure.
No continuous representative, boundary trace, Green normalization or capacity
identification is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

variable (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

theorem exteriorHomogeneousGraph_sobolev_on_bounded {n : ℕ}
    (hp : 1 < p) (hpq : p ≤ q) (w : exteriorHomogeneousGraph p q n)
    {D : Set (Space n)} (hDb : Bornology.IsBounded D) :
    SobolevPair p D (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) := by
  obtain ⟨φ, hφ, hlu, hlg⟩ := exteriorHomogeneousGraph_smooth_approximation p q w
  exact localSobolevPair_of_smooth_mixed_limits hp hpq hφ
    (Lp.memLp w.1.1) (Lp.memLp w.1.2) hlu hlg hDb

set_option maxHeartbeats 1000000 in
theorem exteriorGlobalPlateau_minimum_smooth_equation {n : ℕ} (hp : 1 < p)
    {U : Set (Space n)} (w : exteriorHomogeneousGraph p q n)
    (hw : w ∈ exteriorGlobalPlateauClass p q U)
    (hm : ∀ z ∈ exteriorGlobalPlateauClass p q U, ‖w.1.2‖^p ≤ ‖z.1.2‖^p)
    {φ : Space n → ℝ} (hφ : SmoothTest (closure U)ᶜ φ) :
    (∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) = 0 := by
  have hφu : MemLp φ (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) hφ.1 hφ.2.1
  have hφg : MemLp (gradient φ) (ENNReal.ofReal p) volume :=
    BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hφ.1 hφ.2.1
  let z : ExteriorScalarLp q n × ExteriorVectorLp p n :=
    (hφu.toLp φ, hφg.toLp (gradient φ))
  have hz : z ∈ exteriorSmoothGraph p q n :=
    ⟨φ, ⟨hφ.1, hφ.2.1, subset_univ _⟩, MemLp.coeFn_toLp hφu, MemLp.coeFn_toLp hφg⟩
  let v : exteriorHomogeneousGraph p q n :=
    ⟨z, (exteriorSmoothGraph p q n).le_topologicalClosure hz⟩
  have hvu : (v.1.1 : Space n → ℝ) =ᵐ[volume] φ := MemLp.coeFn_toLp hφu
  have hvg : (v.1.2 : Space n → Space n) =ᵐ[volume] gradient φ := MemLp.coeFn_toLp hφg
  have hφ0 (x : Space n) (hx : x ∈ U) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => (hφ.2.2 ht) (subset_closure hx))
  have hwu (t : ℝ) : ((w+t • v).1.1 : Space n → ℝ) =ᵐ[volume]
      (fun x => (w.1.1 : Space n → ℝ) x+t • φ x) := by
    filter_upwards [Lp.coeFn_add w.1.1 (t • v.1.1), Lp.coeFn_smul t v.1.1, hvu]
      with x ha hs hv
    change ((w.1.1+t • v.1.1 : ExteriorScalarLp q n) : Space n → ℝ) x = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply, hv]
  have hwg (t : ℝ) : ((w+t • v).1.2 : Space n → Space n) =ᵐ[volume]
      (fun x => (w.1.2 : Space n → Space n) x+t • gradient φ x) := by
    filter_upwards [Lp.coeFn_add w.1.2 (t • v.1.2), Lp.coeFn_smul t v.1.2, hvg]
      with x ha hs hv
    change ((w.1.2+t • v.1.2 : ExteriorVectorLp p n) : Space n → Space n) x = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply, hv]
  have ht (t : ℝ) : w+t • v ∈ exteriorGlobalPlateauClass p q U := by
    filter_upwards [hw, hwu t] with x hx he
    intro hxU
    rw [he, hφ0 x hxU, smul_zero, add_zero]
    exact hx hxU
  let F : ℝ → ℝ := fun t => ∫ x, ‖(w.1.2 : Space n → Space n) x+t • gradient φ x‖^p ∂volume
  have he (t : ℝ) : ‖(w+t • v).1.2‖^p = F t := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    exact integral_congr_ae ((hwg t).fun_comp (fun a => ‖a‖^p))
  have hzero : ‖w.1.2‖^p = F 0 := by simpa only [zero_smul, add_zero] using he 0
  have hlocal : IsLocalMin F 0 := by
    apply Eventually.of_forall
    intro t
    rw [←he t, ←hzero]
    exact hm (w+t • v) (ht t)
  have hd : HasDerivAt F (p*(∫ x, inner ℝ (pFlux p ((w.1.2 : Space n → Space n) x))
      (gradient φ x) ∂volume)) 0 := by
    convert! hasDerivAt_integral_energy_line hp (Lp.memLp w.1.2) hφg using 1 <;>
      simp only [F]
  have hh := hlocal.hasDerivAt_eq_zero hd
  exact (mul_eq_zero.mp hh).resolve_left (zero_lt_one.trans hp).ne'

theorem exteriorGlobalPlateau_minimum_weakPHarmonic {n : ℕ} (hp : 1 < p)
    (hpq : p ≤ q) {U : Set (Space n)} (w : exteriorHomogeneousGraph p q n)
    (hw : w ∈ exteriorGlobalPlateauClass p q U)
    (hm : ∀ z ∈ exteriorGlobalPlateauClass p q U, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    WeakPHarmonicPair p (closure U)ᶜ (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) := by
  apply weakPHarmonicPair_of_smooth_test_equation hp isClosed_closure.isOpen_compl
    (fun D hD => exteriorHomogeneousGraph_sobolev_on_bounded p q hp hpq w hD.2.1)
  intro D hD φ hφ
  have hφE : SmoothTest (closure U)ᶜ φ := ⟨hφ.1, hφ.2.1,
    hφ.2.2.trans (subset_closure.trans hD.2.2)⟩
  have he : (∫ x in D, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) =
      ∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg : gradient φ x = 0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      (fun ht => hx (hφ.2.2 ht))
    simp only [fluxPairing, hg, inner_zero_right]
  rw [he]
  exact exteriorGlobalPlateau_minimum_smooth_equation p q hp w hw hm hφE

/-- Actual function-valued exterior weak solution in the subcritical range,
constructed from smooth compact data. The inner unit condition is a.e. on an
open neighborhood; no thin-set trace or selected pointwise representative is asserted. -/
theorem exists_global_finite_energy_plateau_potential {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) {U : Set (Space n)}
    (_hU : IsOpen U) (hUc : IsCompact (closure U)) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ᵐ x ∂volume, x ∈ U → u x = 1) ∧
      WeakPHarmonicPair p (closure U)ᶜ u g ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, SmoothTest univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume)
          atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume)
          atTop (𝓝 0) := by
  let q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hpq : p ≤ q := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (hp.le.trans hpq)⟩
  obtain ⟨w, hw, hm⟩ := exists_exteriorGlobalPlateauClass_minimum p q hp hpn rfl hUc
  refine ⟨(w.1.1 : Space n → ℝ), (w.1.2 : Space n → Space n), Lp.memLp _, Lp.memLp _, hw,
    exteriorGlobalPlateau_minimum_weakPHarmonic p q hp hpq w hw hm, ?_⟩
  exact exteriorHomogeneousGraph_smooth_approximation p q w

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorGlobalPotential

#print axioms BMCompactPDE.isClosed_exteriorHomogeneousGraph
#print axioms BMCompactPDE.exteriorHomogeneousGraph_scalar_bound
#print axioms BMCompactPDE.exists_exteriorHomogeneousGradient_antilipschitz
#print axioms BMCompactPDE.exteriorHomogeneousGraph_smooth_approximation
#print axioms BMCompactPDE.isClosed_exteriorGlobalPlateauClass
#print axioms BMCompactPDE.convex_exteriorGlobalPlateauClass
#print axioms BMCompactPDE.exteriorGlobalPlateauClass_nonempty
#print axioms BMCompactPDE.exists_exteriorGlobalPlateauClass_minimum
#print axioms BMCompactPDE.exteriorHomogeneousGraph_sobolev_on_bounded
#print axioms BMCompactPDE.exteriorGlobalPlateau_minimum_smooth_equation
#print axioms BMCompactPDE.exteriorGlobalPlateau_minimum_weakPHarmonic
#print axioms BMCompactPDE.exists_global_finite_energy_plateau_potential
