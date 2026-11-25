import NonlinearW0Graph
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.FieldSimp

/-! Bounded-domain W0 Poincare for every p>1, including p=n and p>n.
For p>=n, apply smooth GNS at a=n*p/(n+p), then lower the gradient
exponent on the finite-measure domain. The a=1 endpoint is used only for
smooth functions. Actual W0(p) approximation transfers the result; no
endpoint Sobolev predicate, Poincare premise or solution is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private theorem smooth_poincare_aux {n : ℕ} {p a : ℝ}
    (hp : 1<p) (ha : 1≤a) (han : a<(n:ℝ)) (hap : a≤p)
    (hai : a⁻¹-(n:ℝ)⁻¹≤p⁻¹) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ (ENNReal.ofReal p) (volume.restrict D) ≤
        C*eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D) := by
  let A : ℝ≥0 := a.toNNReal
  let P : ℝ≥0 := p.toNNReal
  have ha0 : 0<a := zero_lt_one.trans_le ha
  have hp0 : 0<p := zero_lt_one.trans hp
  have hAr : (A:ℝ)=a := by simp [A,Real.toNNReal_of_nonneg ha0.le]
  have hPr : (P:ℝ)=p := by simp [P,Real.toNNReal_of_nonneg hp0.le]
  have hAe : (A:ℝ≥0∞)=ENNReal.ofReal a := rfl
  have hPe : (P:ℝ≥0∞)=ENNReal.ofReal p := rfl
  let B := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space n)) D A P
  let M : ℝ≥0 := (volume D).toNNReal^(1/a-1/p)
  have hr : 0≤1/a-1/p := sub_nonneg.mpr (one_div_le_one_div_of_le ha0 hap)
  have hM : (M:ℝ≥0∞)=(volume D)^(1/a-1/p) := by
    dsimp only [M]
    rw [ENNReal.coe_rpow_of_nonneg _ hr,ENNReal.coe_toNNReal hDb.measure_lt_top.ne]
  refine ⟨B*M,?_⟩
  intro φ hφ
  have hs : Function.support φ ⊆ D := (subset_tsupport φ).trans hφ.2.2
  have hgs : Function.support (gradient φ) ⊆ D := by
    intro x hx
    by_contra hxn
    exact hx (BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      (fun h => hxn (hφ.2.2 h)))
  have hA1 : 1≤A := by exact_mod_cast (hAr.symm ▸ ha)
  have hAn : A<Module.finrank ℝ (Space n) := by
    apply NNReal.coe_lt_coe.mp
    simpa only [hAr,Space,finrank_euclideanSpace,Fintype.card_fin,NNReal.coe_natCast] using han
  have hAi : (A:ℝ)⁻¹-(Module.finrank ℝ (Space n):ℝ)⁻¹≤(P:ℝ)⁻¹ := by
    simpa only [hAr,hPr,Space,finrank_euclideanSpace,Fintype.card_fin] using hai
  have he := eLpNorm_le_eLpNorm_fderiv_of_le (volume : Measure (Space n))
    (hφ.1.of_le (by simp) : ContDiff ℝ 1 φ) hs hA1 hAn hAi hDb
  have hgNorm : eLpNorm (fderiv ℝ φ) (ENNReal.ofReal a) volume =
      eLpNorm (gradient φ) (ENNReal.ofReal a) volume := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall (fun x => by
      simpa only [gradient] using
        ((toDual ℝ (Space n)).symm.norm_map (fderiv ℝ φ x)).symm)
  rw [hAe,hPe,hgNorm] at he
  have heD : eLpNorm φ (ENNReal.ofReal p) (volume.restrict D) ≤
      B*eLpNorm (gradient φ) (ENNReal.ofReal a) (volume.restrict D) := by
    simpa only [eLpNorm_restrict_eq_of_support_subset hs,
      eLpNorm_restrict_eq_of_support_subset hgs] using he
  have hgrad := (hφ.sobolevPair hp).2.2.1.1
  have hl := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (ENNReal.ofReal_le_ofReal hap) hgrad
  have hlD : eLpNorm (gradient φ) (ENNReal.ofReal a) (volume.restrict D) ≤
      M*eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D) := by
    simpa only [ENNReal.toReal_ofReal ha0.le,ENNReal.toReal_ofReal hp0.le,
      Measure.restrict_apply_univ,←hM,mul_comm] using hl
  calc
    eLpNorm φ (ENNReal.ofReal p) (volume.restrict D) ≤
        (B:ℝ≥0∞)*(M*eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D)) :=
      heD.trans (mul_le_mul_right hlD (B:ℝ≥0∞))
    _ = _ := by rw [ENNReal.coe_mul,mul_assoc]

theorem exists_smooth_Lp_poincare_constant_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ (ENNReal.ofReal p) (volume.restrict D) ≤
        C*eLpNorm (gradient φ) (ENNReal.ofReal p) (volume.restrict D) := by
  by_cases hpn : p<(n:ℝ)
  · exact exists_smooth_Lp_poincare_constant hp hpn hDb
  have hnp : (n:ℝ)≤p := le_of_not_gt hpn
  have hn2 : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ)<(n:ℝ) := by linarith
  have hp0 : 0<p := zero_lt_one.trans hp
  have hd : 0<(n:ℝ)+p := add_pos hn0 hp0
  let a : ℝ := (n:ℝ)*p/((n:ℝ)+p)
  have ha1 : 1≤a := by
    apply (le_div_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_right hn2 hp0.le
    nlinarith
  have han : a<(n:ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [sq_pos_of_pos hn0]
  have hap : a≤p := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg p]
  have hi : a⁻¹-(n:ℝ)⁻¹=p⁻¹ := by
    dsimp only [a]
    field_simp
    <;> ring
  exact smooth_poincare_aux hp ha1 han hap hi.le hDb

theorem exists_W0_Lp_poincare_constant_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ {u : Space n → ℝ} {g : Space n → Space n},
      ZeroBoundarySobolevPair p D u g →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict D) ≤
        C*eLpNorm g (ENNReal.ofReal p) (volume.restrict D) := by
  obtain ⟨C,hC⟩ := exists_smooth_Lp_poincare_constant_allp hp hn hDb
  refine ⟨C,?_⟩
  intro u g hu
  obtain ⟨hs,φ,hφ,huLim,hgLim⟩ := hu
  let q := ENNReal.ofReal p
  let μ := volume.restrict D
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hφm (j : ℕ) := (hφ j).sobolevPair hp
  have hbound (j : ℕ) : eLpNorm u q μ ≤
      eLpNorm (φ j-u) q μ+C*(eLpNorm (fun x => gradient (φ j) x-g x) q μ+eLpNorm g q μ) := by
    have ha := eLpNorm_add_le (hs.2.1.sub (hφm j).2.1).1 (hφm j).2.1.1 hq
    rw [sub_add_cancel,eLpNorm_sub_comm] at ha
    have hb := eLpNorm_add_le ((hφm j).2.2.1.sub hs.2.2.1).1 hs.2.2.1.1 hq
    rw [sub_add_cancel] at hb
    exact ha.trans (add_le_add le_rfl ((hC _ (hφ j)).trans
      (mul_le_mul_right hb (C:ℝ≥0∞))))
  have hinner := hgLim.add_const (eLpNorm g q μ)
  rw [zero_add] at hinner
  have hmul : Tendsto (fun j => (C:ℝ≥0∞)*(eLpNorm (fun x => gradient (φ j) x-g x) q μ+eLpNorm g q μ))
      atTop (𝓝 ((C:ℝ≥0∞)*eLpNorm g q μ)) :=
    ENNReal.Tendsto.const_mul hinner (Or.inr ENNReal.coe_ne_top)
  have htotal := huLim.add hmul
  rw [zero_add] at htotal
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htotal (Eventually.of_forall hbound)

variable (p : ℝ) [Fact (1≤ENNReal.ofReal p)]

theorem exists_w0Lp_scalar_norm_bound_allp (hp : 1<p) {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ w : w0LpGraph p hp n Ω, ‖w.1.1‖≤C*‖w.1.2‖ := by
  obtain ⟨C,hC⟩ := exists_W0_Lp_poincare_constant_allp hp hn hΩb
  refine ⟨C,?_⟩
  intro w
  have he := hC w.2
  have hfin : (C:ℝ≥0∞)*eLpNorm (w.1.2 : Space n → Space n) (ENNReal.ofReal p) (volume.restrict Ω)≠(∞:ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top w.1.2)
  have hr := ENNReal.toReal_mono hfin he
  simpa only [Lp.norm_def,ENNReal.toReal_mul,ENNReal.coe_toReal] using hr

theorem exists_w0LpGradient_antilipschitz_allp (hp : 1<p) {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ≥0, AntilipschitzWith K (w0LpGradient p hp n Ω) := by
  obtain ⟨C,hC⟩ := exists_w0Lp_scalar_norm_bound_allp p hp hn hΩb
  let K : ℝ≥0 := max C 1
  have hCK : (C:ℝ)≤(K:ℝ) := by exact_mod_cast (le_max_left C 1)
  have hK1 : (1:ℝ)≤(K:ℝ) := by exact_mod_cast (le_max_right C 1)
  refine ⟨K,(w0LpGradient p hp n Ω).antilipschitz_of_bound ?_⟩
  intro w
  change max ‖w.1.1‖ ‖w.1.2‖≤(K:ℝ)*‖w.1.2‖
  exact max_le ((hC w).trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg _)))
    (le_mul_of_one_le_left (norm_nonneg _) hK1)

theorem isClosed_w0LpGradientRange_allp (hp : 1<p) {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    IsClosed (w0LpGradientRange p hp n Ω : Set (VectorLp p n Ω)) := by
  letI : CompleteSpace (w0LpGraph p hp n Ω) := (isClosed_w0LpGraph p hp n Ω).completeSpace_coe
  obtain ⟨K,hK⟩ := exists_w0LpGradient_antilipschitz_allp p hp hn hΩb
  exact hK.isClosed_range (w0LpGradient p hp n Ω).uniformContinuous

end BMCompactPDE
#print axioms BMCompactPDE.exists_smooth_Lp_poincare_constant_allp
#print axioms BMCompactPDE.exists_W0_Lp_poincare_constant_allp
#print axioms BMCompactPDE.exists_w0Lp_scalar_norm_bound_allp
#print axioms BMCompactPDE.exists_w0LpGradient_antilipschitz_allp
#print axioms BMCompactPDE.isClosed_w0LpGradientRange_allp
