import GradientAnalyticBatch
import RootAllpDirichlet
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Construct regularized weak Dirichlet solutions through the actual W0 graph
and the genuine Hilbert augmentation (epsilon,g). No minimizer, weak solution,
classical regularity or A5 approximation premise is an input to the final
construction. Smoothness of the explicit flux is not smoothness of a solution.
The lifted minimum argument adapts the already checked RootAllpDirichlet proof.
-/
noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal
namespace BMCompactPDE

abbrev GradientAugmentedSpace (n : ℕ) := WithLp 2 (ℝ × Space n)

def gradientAugmentedInjection (n : ℕ) : Space n →L[ℝ] GradientAugmentedSpace n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Space n)).symm.toContinuousLinearMap.comp
    ((0 : Space n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space n)))

theorem gradientAugmentedInjection_apply {n : ℕ} (v : Space n) :
    gradientAugmentedInjection n v=WithLp.toLp 2 ((0 : ℝ),v) := rfl

theorem gradientAugmentedInjection_norm {n : ℕ} (v : Space n) :
    ‖gradientAugmentedInjection n v‖=‖v‖ := by
  rw [gradientAugmentedInjection_apply,WithLp.prod_norm_eq_of_L2]
  simp [WithLp.fst,WithLp.snd]

theorem gradientAugmentedFlux_pairing {n : ℕ} (p ε : ℝ) (v h : Space n) :
    inner ℝ (pFlux p (WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n))
        (gradientAugmentedInjection n h)=
      inner ℝ ((ε^2+‖v‖^2)^((p-2)/2) • v) h := by
  rw [gradientAugmentedInjection_apply]
  have hn : ‖(WithLp.toLp 2 (ε,v) : GradientAugmentedSpace n)‖^(p-2)=
      (ε^2+‖v‖^2)^((p-2)/2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.toLp_fst,WithLp.toLp_snd,
      Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg ‖v‖))]
    congr 1
    ring
  simp only [pFlux,real_inner_smul_left,WithLp.prod_inner_apply,
    WithLp.ofLp_smul,WithLp.ofLp_toLp,Prod.smul_fst,Prod.smul_snd,
    inner_zero_right,zero_add]
  rw [hn]

/-- The explicit regularized equation is tested against every actual full-W0
pair on the bounded domain. This definition contains only the actual Sobolev
graph and integrals; no regularity or existence clause is smuggled into it. -/
def GlobalWeakRegularizedSourcePair {n : ℕ} (p ε c : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1<p ∧ IsOpen Ω ∧ SobolevPair p Ω u g ∧
    ∀ θ : Space n → ℝ, ∀ k : Space n → Space n,
      ZeroBoundarySobolevPair p Ω θ k →
      Integrable (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x))
        (volume.restrict Ω) ∧
      (∫ x in Ω,inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x))=
        c*(∫ x in Ω,θ x)

private theorem gradient_memLp_flux_generic {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℝ} (hp : 1<p) {μ : Measure α} {g : α → E}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    MemLp (fun x => pFlux p (g x)) (ENNReal.ofReal (p/(p-1))) μ := by
  have hm : 0<p-1 := sub_pos.mpr hp
  have hn : MemLp (fun x => ‖g x‖^(p-1)) (ENNReal.ofReal (p/(p-1))) μ := by
    simpa only [ENNReal.toReal_ofReal hm.le,← ENNReal.ofReal_div_of_pos hm]
      using hg.norm_rpow_div (ENNReal.ofReal (p-1))
  have hmeas := (continuous_pFlux hp).comp_aestronglyMeasurable hg.1
  apply (memLp_norm_iff hmeas).mp
  simpa only [norm_pFlux hp] using hn

section Lift
variable (p : ℝ) [Fact (1≤ENNReal.ofReal p)] (hp : 1<p)

def gradientAugmentedLpInjection {n : ℕ} (Ω : Set (Space n)) :
    VectorLp p n Ω →L[ℝ]
      Lp (GradientAugmentedSpace n) (ENNReal.ofReal p) (volume.restrict Ω) :=
  (gradientAugmentedInjection n).compLpL (ENNReal.ofReal p) (volume.restrict Ω)

theorem gradientAugmentedLpInjection_norm {n : ℕ} {Ω : Set (Space n)}
    (F : VectorLp p n Ω) : ‖gradientAugmentedLpInjection p Ω F‖=‖F‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  apply congrArg ENNReal.toReal
  rw [← eLpNorm_norm (gradientAugmentedLpInjection p Ω F),← eLpNorm_norm F]
  apply eLpNorm_congr_ae
  filter_upwards [(gradientAugmentedInjection n).coeFn_compLpL F] with x hx
  change ‖((gradientAugmentedInjection n).compLpL (ENNReal.ofReal p) (volume.restrict Ω) F) x‖=‖F x‖
  rw [hx,gradientAugmentedInjection_norm]

set_option maxHeartbeats 1000000 in
theorem exists_w0LpLiftedEnergy_minimum {n : ℕ} (hn : 2≤n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [StrictConvexSpace ℝ E] [ProperSpace E]
    (T : VectorLp p n Ω →L[ℝ] Lp E (ENNReal.ofReal p) (volume.restrict Ω))
    (hT : ∀ F,‖T F‖=‖F‖)
    (F : Lp E (ENNReal.ofReal p) (volume.restrict Ω)) (c : ℝ) :
    ∃ v : w0LpGraph p hp n Ω, ∀ z : w0LpGraph p hp n Ω,
      ‖F+T v.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb v) ≤
        ‖F+T z.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb z) := by
  have hp0 : 0<p := zero_lt_one.trans hp
  letI : CompleteSpace (w0LpGraph p hp n Ω) :=
    (isClosed_w0LpGraph p hp n Ω).completeSpace_coe
  obtain ⟨K,hK,L,hL,hload⟩ := exists_w0LpLoadCLM_allp p hp hn hΩb
  let J : w0LpGraph p hp n Ω → ℝ := fun w => ‖F+T w.1.2‖^p-p*c*L w
  have hJ (w : w0LpGraph p hp n Ω) : J w=‖F+T w.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb w) := by
    simp only [J,w0LpLoadLinear_apply,hL w]
  have hcont : Continuous J := by
    have hg : Continuous (fun w : w0LpGraph p hp n Ω => F+T w.1.2) :=
      continuous_const.add (T.continuous.comp (w0LpGradient p hp n Ω).continuous)
    exact (hg.norm.rpow_const (fun _ => Or.inr hp0.le)).sub (L.continuous.const_mul (p*c))
  let B := |c| * K
  have hB : 0≤B := mul_nonneg (abs_nonneg _) hK
  let d := -p*(B^(p/(p-1))/(p/(p-1)))-p*B*‖F‖
  have hbdd : BddBelow (J '' (univ : Set (w0LpGraph p hp n Ω))) := by
    refine ⟨d,?_⟩
    rintro _ ⟨w,_,rfl⟩
    let t := ‖F+T w.1.2‖
    have ht : 0≤t := norm_nonneg _
    have hgrad : ‖w.1.2‖≤t+‖F‖ := by
      calc
        ‖w.1.2‖ = ‖(F+T w.1.2)-F‖ := by rw [add_sub_cancel_left,hT]
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
    obtain ⟨Q,hQ0,hQ⟩ := source_energy_coercive_allp hp hB (a/p+B*‖F‖)
    refine ⟨C*(Q+‖F‖),?_⟩
    intro w _ hw
    let t := ‖F+T w.1.2‖
    have hgrad : ‖w.1.2‖≤t+‖F‖ := by
      calc
        ‖w.1.2‖ = ‖(F+T w.1.2)-F‖ := by rw [add_sub_cancel_left,hT]
        _ ≤ t+‖F‖ := norm_sub_le _ _
    have hl : |L w|≤K*(t+‖F‖) :=
      (hload w).trans (mul_le_mul_of_nonneg_left hgrad hK)
    have hc : c*L w≤B*(t+‖F‖) := by
      calc
        c*L w ≤ |c*L w| := le_abs_self _
        _ = |c| * |L w| := abs_mul _ _
        _ ≤ |c| * (K*(t+‖F‖)) := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
        _ = _ := by dsimp [B]; ring
    have ht : t≤Q := by
      by_contra hnot
      have hlarger := hQ t (lt_of_not_ge hnot).le
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
      (E := E) (μ := volume.restrict Ω) hp (‖F‖+R) (ε/C) (div_pos hε hC)
    refine ⟨κ,hκ,?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖≤(A:ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm,w0LpGradient_apply] using hA.le_mul_dist x y
    have he : ε≤C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hdiff : (F+T x.1.2)-(F+T y.1.2)=T (x.1.2-y.1.2) := by rw [map_sub]; abel
    have hsep : ε/C≤‖(F+T x.1.2)-(F+T y.1.2)‖ := by
      rw [hdiff,hT]
      exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖F+T x.1.2‖≤‖F‖+R := (norm_add_le _ _).trans
      (add_le_add le_rfl (by rw [hT]; exact (le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx))
    have hFy : ‖F+T y.1.2‖≤‖F‖+R := (norm_add_le _ _).trans
      (add_le_add le_rfl (by rw [hT]; exact (le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy))
    have hcl := hfield (F+T x.1.2) (F+T y.1.2) hFx hFy hsep
    have hm : F+T ((1/2:ℝ) • x+(1/2:ℝ) • y).1.2 =
        (1/2:ℝ) • ((F+T x.1.2)+(F+T y.1.2)) := by
      change F+T ((1/2:ℝ) • x.1.2+(1/2:ℝ) • y.1.2)=_
      rw [map_add,map_smul,map_smul]
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


end Lift

set_option maxHeartbeats 1000000 in
private theorem gradient_lifted_minimum_Euler
    {n : ℕ} {p c : ℝ} (hp : 1<p) [Fact (1≤ENNReal.ofReal p)]
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : VectorLp p n Ω →L[ℝ] Lp E (ENNReal.ofReal p) (volume.restrict Ω))
    (F : Lp E (ENNReal.ofReal p) (volume.restrict Ω))
    (v : w0LpGraph p hp n Ω)
    (hv : ∀ z : w0LpGraph p hp n Ω,
      ‖F+T v.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb v) ≤
        ‖F+T z.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb z))
    (z : w0LpGraph p hp n Ω) :
    Integrable (fun x => inner ℝ (pFlux p ((F+T v.1.2) x)) ((T z.1.2) x))
      (volume.restrict Ω) ∧
    (∫ x in Ω,inner ℝ (pFlux p ((F+T v.1.2) x)) ((T z.1.2) x))=
      c*(w0LpLoadLinear p hp hΩb z) := by
  let μ := volume.restrict Ω
  let G : Lp E (ENNReal.ofReal p) μ := F+T v.1.2
  let H : Lp E (ENNReal.ofReal p) μ := T z.1.2
  let L := w0LpLoadLinear p hp hΩb
  let I : ℝ := ∫ x,inner ℝ (pFlux p (G x)) (H x) ∂μ
  let J : ℝ → ℝ := fun t => (∫ x,‖G x+t • H x‖^p ∂μ)-p*c*(t*L z)
  have hnorm (t : ℝ) : ‖G+t • H‖^p=∫ x,‖G x+t • H x‖^p ∂μ := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add G (t • H),Lp.coeFn_smul t H] with x ha hs
    rw [ha,Pi.add_apply,hs]
    simp only [Pi.smul_apply]
  have hnorm0 : ‖G‖^p=∫ x,‖G x‖^p ∂μ := by
    simpa only [zero_smul,add_zero] using hnorm 0
  have hlocal : IsLocalMin J 0 := by
    apply Eventually.of_forall
    intro t
    have hm := hv (v+t • z)
    have hfield : F+T (v+t • z).1.2=G+t • H := by
      change F+T (v.1.2+t • z.1.2)=G+t • H
      simp only [map_add,map_smul,G,H]
      module
    rw [hfield] at hm
    change ‖G‖^p-p*c*L v≤‖G+t • H‖^p-p*c*L (v+t • z) at hm
    rw [map_add,map_smul,smul_eq_mul,hnorm t,hnorm0] at hm
    dsimp only [J]
    simp only [zero_smul,add_zero,zero_mul,mul_zero,sub_zero]
    nlinarith only [hm]
  have hd : HasDerivAt J (p*I-p*c*L z) 0 := by
    convert! (hasDerivAt_integral_energy_line hp (Lp.memLp G) (Lp.memLp H)).sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (L z)).const_mul (p*c)) using 1 <;>
      simp only [J,I,μ,Pi.sub_apply,one_mul,id_eq]
  have hz := hlocal.hasDerivAt_eq_zero hd
  have hz' : p*(I-c*L z)=0 := by nlinarith only [hz]
  have hi : I=c*L z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (zero_lt_one.trans hp).ne')
  letI := holderConjugate_p_dual hp
  exact ⟨inner_integrable_of_dual_memLp (gradient_memLp_flux_generic hp (Lp.memLp G))
    (Lp.memLp H),hi⟩

set_option maxHeartbeats 1000000 in
theorem exists_global_weak_regularized_Dirichlet
    {n : ℕ} {p : ℝ} (hp : 1<p) (hn : 2≤n) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (ε c : ℝ)
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ w : Space n → ℝ, ∃ gw : Space n → Space n,
      ZeroBoundarySobolevPair p Ω w gw ∧
      GlobalWeakRegularizedSourcePair p ε c Ω (f+w) (gf+gw) := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let μ := volume.restrict Ω
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let T := gradientAugmentedLpInjection p Ω
  let B0 : GradientAugmentedSpace n := WithLp.toLp 2 (ε,(0 : Space n))
  have hB : MemLp (fun _ : Space n => B0) (ENNReal.ofReal p) μ := memLp_const B0
  let B := hB.toLp (fun _ : Space n => B0)
  let Fg := hf.2.2.1.toLp gf
  let F := B+T Fg
  obtain ⟨v,hv⟩ := exists_w0LpLiftedEnergy_minimum p hp hn hΩb T
    (fun H => gradientAugmentedLpInjection_norm p H) F c
  let w : Space n → ℝ := v.1.1
  let gw : Space n → Space n := v.1.2
  let g : Space n → Space n := gf+gw
  have hTa (U : VectorLp p n Ω) : T U=ᵐ[μ] fun x => gradientAugmentedInjection n (U x) :=
    (gradientAugmentedInjection n).coeFn_compLpL U
  have hGa : (F+T v.1.2)=ᵐ[μ] fun x => WithLp.toLp 2 (ε,g x) := by
    filter_upwards [Lp.coeFn_add F (T v.1.2),Lp.coeFn_add B (T Fg),hTa Fg,hTa v.1.2,
      hB.coeFn_toLp,hf.2.2.1.coeFn_toLp] with x hsum hF hTF hTv hBx hgfx
    rw [hsum,Pi.add_apply,hF,Pi.add_apply,hBx,hTF,hTv,hgfx]
    change WithLp.toLp 2 (ε,(0 : Space n))+
      gradientAugmentedInjection n (gf x)+gradientAugmentedInjection n (gw x)=_
    rw [gradientAugmentedInjection_apply,gradientAugmentedInjection_apply,
      ← WithLp.toLp_add,← WithLp.toLp_add]
    congr 1
    ext <;> simp [g,Pi.add_apply]
  refine ⟨w,gw,v.2,hp,hΩ,hf.add v.2.1,?_⟩
  intro θ k hθ
  obtain ⟨z,hzu,hzg⟩ := hθ.exists_w0LpGraph_representatives hp
  have hE := gradient_lifted_minimum_Euler hp hΩb T F v hv z
  have hpair : (fun x => inner ℝ (pFlux p ((F+T v.1.2) x)) ((T z.1.2) x))=ᵐ[μ]
      (fun x => inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x)) := by
    filter_upwards [hGa,hTa z.1.2,hzg] with x hG hTz hz
    rw [hG,hTz,hz]
    exact gradientAugmentedFlux_pairing p ε (g x) (k x)
  have hL : w0LpLoadLinear p hp hΩb z=∫ x in Ω,θ x := by
    rw [w0LpLoadLinear_apply]
    exact integral_congr_ae hzu
  refine ⟨hE.1.congr hpair,?_⟩
  calc
    _ = ∫ x in Ω,inner ℝ (pFlux p ((F+T v.1.2) x)) ((T z.1.2) x) :=
      (integral_congr_ae hpair).symm
    _ = c*(w0LpLoadLinear p hp hΩb z) := hE.2
    _ = c*(∫ x in Ω,θ x) := by rw [hL]

end BMCompactPDE
#print axioms BMCompactPDE.gradientAugmentedInjection_apply
#print axioms BMCompactPDE.gradientAugmentedInjection_norm
#print axioms BMCompactPDE.gradientAugmentedFlux_pairing
#print axioms BMCompactPDE.gradientAugmentedLpInjection_norm
#print axioms BMCompactPDE.exists_w0LpLiftedEnergy_minimum
#print axioms BMCompactPDE.exists_global_weak_regularized_Dirichlet
