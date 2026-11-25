import RootAllpPoincare
import NonlinearAnalyticBatch

/-! Actual bounded nonlinear Dirichlet/source existence for all p>1,n>=2.
The V8 construction proof bodies are generalized using the newly proved
all-p Poincare and gradient inverse. No minimizer, source solution, selected
regularity or pointwise boundary conclusion is supplied as a premise.
The boundary conclusion is the genuine zero-boundary Sobolev correction.
Exact internal-source adaptation is recorded separately; baseline immutable. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology
namespace BMCompactPDE
theorem exists_W0_source_load_bound_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {Ω : Set (Space n)}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0≤K ∧ ∀ {w : Space n → ℝ} {gw : Space n → Space n},
      ZeroBoundarySobolevPair p Ω w gw →
        |∫ x in Ω,w x|≤K*(eLpNorm gw (ENNReal.ofReal p) (volume.restrict Ω)).toReal := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  obtain ⟨C,hC⟩ := exists_W0_Lp_poincare_constant_allp hp hn hΩb
  let μ := volume.restrict Ω
  let M : ℝ≥0∞ := μ univ^(1-1/p)
  have hp0 : 0<p := zero_lt_one.trans hp
  have he : 0≤1-1/p := sub_nonneg.mpr ((div_le_iff₀ hp0).mpr (by linarith))
  have hM : M≠(∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ)
  refine ⟨(C : ℝ)*M.toReal,mul_nonneg C.coe_nonneg ENNReal.toReal_nonneg,?_⟩
  intro w gw hw
  have hLp : eLpNorm w 1 μ≤eLpNorm w (ENNReal.ofReal p) μ*M := by
    simpa only [ENNReal.toReal_one,ENNReal.toReal_ofReal hp0.le,div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (ENNReal.one_le_ofReal.mpr hp.le) hw.1.2.1.1
  have hI : ‖∫ x,w x ∂μ‖ₑ≤eLpNorm w 1 μ := by
    simpa only [eLpNorm_one_eq_lintegral_enorm] using
      (enorm_integral_le_lintegral_enorm (μ := μ) w)
  have hbound : ‖∫ x,w x ∂μ‖ₑ≤
      ((C : ℝ≥0∞)*eLpNorm gw (ENNReal.ofReal p) μ)*M :=
    hI.trans (hLp.trans (mul_le_mul_left (hC hw) M))
  have hfinite : ((C : ℝ≥0∞)*eLpNorm gw (ENNReal.ofReal p) μ)*M≠(∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hw.1.2.2.1.eLpNorm_ne_top) hM
  have hr := ENNReal.toReal_mono hfinite hbound
  simp only [toReal_enorm,Real.norm_eq_abs,ENNReal.toReal_mul,ENNReal.coe_toReal] at hr
  convert hr using 1 <;> ring

section Graph
variable (p : ℝ) [Fact (1≤ENNReal.ofReal p)] (hp : 1<p)
theorem exists_w0LpLoadCLM_allp {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0≤K ∧ ∃ L : w0LpGraph p hp n Ω →L[ℝ] ℝ,
      (∀ v, L v = ∫ x in Ω, (v.1.1 : Space n → ℝ) x) ∧
      ∀ v, |L v|≤K*‖v.1.2‖ := by
  obtain ⟨K,hK,hbound⟩ := exists_W0_source_load_bound_allp hp hn hΩb
  let L := w0LpLoadLinear p hp hΩb
  have hv (v : w0LpGraph p hp n Ω) : ‖L v‖≤K*‖v.1.2‖ := by
    simpa only [L,w0LpLoadLinear_apply,Real.norm_eq_abs,Lp.norm_def] using hbound v.2
  have hb (v : w0LpGraph p hp n Ω) : ‖L v‖≤K*‖v‖ := by
    exact (hv v).trans (mul_le_mul_of_nonneg_left (le_max_right ‖v.1.1‖ ‖v.1.2‖) hK)
  refine ⟨K,hK,L.mkContinuous K hb,?_,?_⟩
  · intro v
    rfl
  · intro v
    simpa only [LinearMap.mkContinuous_apply,Real.norm_eq_abs] using hv v

set_option maxHeartbeats 1000000 in
theorem exists_w0LpSourceEnergy_minimum_allp {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    (F : VectorLp p n Ω) (c : ℝ) :
    ∃ v : w0LpGraph p hp n Ω, ∀ z : w0LpGraph p hp n Ω,
      w0LpSourceEnergy p hp hΩb F c v ≤ w0LpSourceEnergy p hp hΩb F c z := by
  have hp0 : 0<p := zero_lt_one.trans hp
  letI : CompleteSpace (w0LpGraph p hp n Ω) :=
    (isClosed_w0LpGraph p hp n Ω).completeSpace_coe
  obtain ⟨K,hK,L,hL,hload⟩ := exists_w0LpLoadCLM_allp p hp hn hΩb
  let J : w0LpGraph p hp n Ω → ℝ := fun w => ‖F+w.1.2‖^p-p*c*L w
  have hJ (w : w0LpGraph p hp n Ω) : J w=w0LpSourceEnergy p hp hΩb F c w := by
    simp only [J,w0LpSourceEnergy,w0LpLoadLinear_apply,hL w]
  have hcont : Continuous J := by
    have hg : Continuous (fun w : w0LpGraph p hp n Ω => F+w.1.2) :=
      continuous_const.add (w0LpGradient p hp n Ω).continuous
    exact (hg.norm.rpow_const (fun _ => Or.inr hp0.le)).sub (L.continuous.const_mul (p*c))
  let B := |c| * K
  have hB : 0≤B := mul_nonneg (abs_nonneg _) hK
  let d := -p*(B^(p/(p-1))/(p/(p-1)))-p*B*‖F‖
  have hbdd : BddBelow (J '' (univ : Set (w0LpGraph p hp n Ω))) := by
    refine ⟨d,?_⟩
    rintro _ ⟨w,_,rfl⟩
    let t := ‖F+w.1.2‖
    have ht : 0≤t := norm_nonneg _
    have hgrad : ‖w.1.2‖≤t+‖F‖ := by
      calc
        ‖w.1.2‖ = ‖(F+w.1.2)-F‖ := by congr 1; abel
        _ ≤ t+‖F‖ := norm_sub_le _ _
    have hl : |L w|≤K*(t+‖F‖) :=
      (hload w).trans (mul_le_mul_of_nonneg_left hgrad hK)
    have hc : c*L w≤B*(t+‖F‖) := by
      calc
        c*L w ≤ |c*L w| := le_abs_self _
        _ = |c| * |L w| := abs_mul _ _
        _ ≤ |c| * (K*(t+‖F‖)) := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        _ = _ := by dsimp [B]; ring
    have hc' := mul_le_mul_of_nonneg_left hc hp0.le
    have hs := mul_le_mul_of_nonneg_left (source_energy_bounded_below_allp hp hB ht) hp0.le
    have he : p*(t^p/p)=t^p := by field_simp [hp0.ne']
    change d≤t^p-p*c*L w
    dsimp only [d]
    nlinarith [hc',hs,he]
  obtain ⟨A,hA⟩ := exists_w0LpGradient_antilipschitz_allp p hp hn hΩb
  let C : ℝ := (A:ℝ)+1
  have hC : 0<C := by dsimp [C]; positivity
  have hinv (w : w0LpGraph p hp n Ω) : ‖w‖≤C*‖w.1.2‖ := by
    have hh : ‖w‖≤(A:ℝ)*‖w.1.2‖ := by
      simpa only [dist_eq_norm,map_zero,sub_zero,w0LpGradient_apply] using hA.le_mul_dist w 0
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ, ∀ w ∈ (univ : Set (w0LpGraph p hp n Ω)),
      J w≤a → ‖w‖≤R := by
    intro a
    obtain ⟨T,hT0,hT⟩ := source_energy_coercive_allp hp hB (a/p+B*‖F‖)
    refine ⟨C*(T+‖F‖),?_⟩
    intro w _ hw
    let t := ‖F+w.1.2‖
    have hgrad : ‖w.1.2‖≤t+‖F‖ := by
      calc
        ‖w.1.2‖ = ‖(F+w.1.2)-F‖ := by congr 1; abel
        _ ≤ t+‖F‖ := norm_sub_le _ _
    have hl : |L w|≤K*(t+‖F‖) :=
      (hload w).trans (mul_le_mul_of_nonneg_left hgrad hK)
    have hc : c*L w≤B*(t+‖F‖) := by
      calc
        c*L w ≤ |c*L w| := le_abs_self _
        _ = |c| * |L w| := abs_mul _ _
        _ ≤ |c| * (K*(t+‖F‖)) := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        _ = _ := by dsimp [B]; ring
    have ht : t≤T := by
      by_contra hnot
      have hlarger := hT t (lt_of_not_ge hnot).le
      have hc' := mul_le_mul_of_nonneg_left hc hp0.le
      have hp' := mul_lt_mul_of_pos_left hlarger hp0
      have he : p*(t^p/p)=t^p := by field_simp [hp0.ne']
      have hae : p*(a/p)=a := by field_simp [hp0.ne']
      change t^p-p*c*L w≤a at hw
      nlinarith [hc',hp',he,hae]
    exact (hinv w).trans (mul_le_mul_of_nonneg_left
      (hgrad.trans (add_le_add ht le_rfl)) hC.le)
  have hgap : ∀ R ε : ℝ, 0<ε → ∃ κ : ℝ, 0<κ ∧
      ∀ x ∈ (univ : Set (w0LpGraph p hp n Ω)), ∀ y ∈ univ,
      ‖x‖≤R → ‖y‖≤R → ε≤‖x-y‖ →
      J ((1/2:ℝ) • x+(1/2:ℝ) • y)≤(J x+J y)/2-κ := by
    intro R ε hε
    obtain ⟨κ,hκ,hfield⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := volume.restrict Ω) hp (‖F‖+R) (ε/C) (div_pos hε hC)
    refine ⟨κ,hκ,?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖≤(A:ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm,w0LpGradient_apply] using hA.le_mul_dist x y
    have he : ε≤C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hdiff : (F+x.1.2)-(F+y.1.2)=x.1.2-y.1.2 := by abel
    have hsep : ε/C≤‖(F+x.1.2)-(F+y.1.2)‖ := by
      rw [hdiff]
      exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖F+x.1.2‖≤‖F‖+R := (norm_add_le _ _).trans
      (add_le_add le_rfl ((le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx))
    have hFy : ‖F+y.1.2‖≤‖F‖+R := (norm_add_le _ _).trans
      (add_le_add le_rfl ((le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy))
    have hcl := hfield (F+x.1.2) (F+y.1.2) hFx hFy hsep
    have hm : F+((1/2:ℝ) • x+(1/2:ℝ) • y).1.2 =
        (1/2:ℝ) • ((F+x.1.2)+(F+y.1.2)) := by
      change F+((1/2:ℝ) • x.1.2+(1/2:ℝ) • y.1.2)=_
      module
    have hl : L ((1/2:ℝ) • x+(1/2:ℝ) • y)=(1/2:ℝ)*L x+(1/2:ℝ)*L y := by
      simp only [map_add,map_smul,smul_eq_mul]
    dsimp only [J]
    rw [hm,hl]
    nlinarith [hcl]
  obtain ⟨v,_,hv⟩ := BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
    (K := (univ : Set (w0LpGraph p hp n Ω))) (by exact ⟨0,mem_univ _⟩)
    isClosed_univ (convex_univ) hcont.continuousOn hbdd hcoercive hgap
  refine ⟨v,fun z => ?_⟩
  simpa only [hJ] using hv z (mem_univ z)

end Graph

theorem exists_weak_source_Dirichlet_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (c : ℝ)
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ w : Space n → ℝ, ∃ gw : Space n → Space n,
      ZeroBoundarySobolevPair p Ω w gw ∧
      WeakPSourcePair p c Ω (f+w) (gf+gw) := by
  have hp0 : 0<p := zero_lt_one.trans hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let μ := volume.restrict Ω
  let F := hf.2.2.1.toLp gf
  obtain ⟨v,hv⟩ := exists_w0LpSourceEnergy_minimum_allp p hp hn hΩb F c
  let w : Space n → ℝ := v.1.1
  let gw : Space n → Space n := v.1.2
  let g : Space n → Space n := gf+gw
  have hg : MemLp g (ENNReal.ofReal p) μ := hf.2.2.1.add v.2.1.2.2.1
  have henergy (z : w0LpGraph p hp n Ω) :
      ‖F+z.1.2‖^p = ∫ x in Ω, ‖gf x+(z.1.2 : Space n → Space n) x‖^p := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral hp0]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add F z.1.2,MemLp.coeFn_toLp hf.2.2.1] with x hsum hF
    rw [hsum]
    change ‖(hf.2.2.1.toLp gf) x+(z.1.2 : Space n → Space n) x‖^p = _
    rw [hF]
  have hmin : ∀ (θ : Space n → ℝ) (h : Space n → Space n),
      ZeroBoundarySobolevPair p Ω θ h →
      (∫ x in Ω, ‖g x‖^p) ≤
        (∫ x in Ω, ‖g x+h x‖^p)-p*c*(∫ x in Ω, θ x) := by
    intro θ h hθ
    obtain ⟨z,hzu,hzg⟩ := hθ.exists_w0LpGraph_representatives hp
    have hL : w0LpLoadLinear p hp hΩb z = ∫ x in Ω, θ x := by
      rw [w0LpLoadLinear_apply]
      exact integral_congr_ae hzu
    have hsumE : (∫ x in Ω, ‖gf x+((v+z).1.2 : Space n → Space n) x‖^p) =
        ∫ x in Ω, ‖g x+h x‖^p := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add v.1.2 z.1.2,hzg] with x hsum hz
      change ‖gf x+((v.1.2+z.1.2 : VectorLp p n Ω) : Space n → Space n) x‖^p = _
      rw [hsum,Pi.add_apply,hz]
      change ‖gf x+(gw x+h x)‖^p = ‖(gf x+gw x)+h x‖^p
      rw [add_assoc]
    have hm := hv (v+z)
    simp only [w0LpSourceEnergy,henergy,map_add,hL,hsumE] at hm
    change (∫ x in Ω, ‖g x‖^p)-p*c*(w0LpLoadLinear p hp hΩb v) ≤
      (∫ x in Ω, ‖g x+h x‖^p)-p*c*((w0LpLoadLinear p hp hΩb v)+(∫ x in Ω, θ x)) at hm
    nlinarith [hm]
  refine ⟨w,gw,v.2,?_⟩
  apply weakPSourcePair_of_sobolev_smooth_source_equation hΩ (hf.add v.2.1)
  intro φ hφ
  have he := (source_flux_identity_of_actual_energy_minimum hp hg hmin
    (hφ.zeroBoundarySobolevPair hp)).2
  simpa only [fluxPairing] using he

theorem exists_weak_harmonic_Dirichlet_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ w : Space n → ℝ, ∃ gw : Space n → Space n,
      ZeroBoundarySobolevPair p Ω w gw ∧
      WeakPHarmonicPair p Ω (f+w) (gf+gw) := by
  obtain ⟨w,gw,hw,hsol⟩ := exists_weak_source_Dirichlet_allp hp hn hΩ hΩb 0 hf
  exact ⟨w,gw,hw,hsol.harmonic_of_source_zero⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_W0_source_load_bound_allp
#print axioms BMCompactPDE.exists_w0LpLoadCLM_allp
#print axioms BMCompactPDE.exists_w0LpSourceEnergy_minimum_allp
#print axioms BMCompactPDE.exists_weak_source_Dirichlet_allp
#print axioms BMCompactPDE.exists_weak_harmonic_Dirichlet_allp
