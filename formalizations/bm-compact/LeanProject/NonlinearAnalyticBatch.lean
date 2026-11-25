import ForcingGlobal
import ForcingLoad
import NonlinearClarkson
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import RadialFoundation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import NonlinearW0Graph
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RootAllpEnergyBatch
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic.Module
import RootW0Linear
import WeakDensity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import RegularityWeightedPDE
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PotentialTwoSidedEnergy
import PotentialLocalBoost

/-! Prospective actual nonlinear analysis; zero proof counts until native PASS.
The four input batches are retained as provenance, with exact maps in NonlinearAnalyticSegments.manifest.json. -/

section AnalyticBlock_ForcingPreExistenceBatch
/- Exact prepared input: ForcingPreExistenceBatch.lean; SHA256 6983e11ea4fe2e4ec8cc083798e7be364694b5a3e035dfcc3d4c79cd2b018a8f. -/

/-! PROSPECTIVE EXACT-BODY BATCH: uncounted until native PASS.
Original authored sources, individual body hashes and import mapping are in ForcingBatches/.
Each retained source body is byte-for-byte unchanged; only import hoisting and explicit EOF section closure are added. -/

section ForcingSegmentForcingCoercivityAll
/- Authored source: ForcingCoercivityAll.lean; exact SHA256 c3b3e40ebf7bc7340ea408be6eca44b6981ad2ef5882226fb6321009cd8fc613. -/

/-! Genuine bounded-below/coercivity for every p>1, from proved Young.
These do not depend on a PDE minimizer, compactness or a desired sublevel
bound. The p>=2 elementary helpers remain separate and unchanged. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace BMCompactPDE

theorem source_energy_bounded_below_allp {p B t : ℝ}
    (hp : 1<p) (hB : 0≤B) (ht : 0≤t) :
    -(B^(p/(p-1))/(p/(p-1)))≤t^p/p-B*t := by
  have hy := Real.young_inequality_of_nonneg ht hB
    (Real.HolderConjugate.conjExponent hp)
  change t*B≤t^p/p+B^(p/(p-1))/(p/(p-1)) at hy
  linarith only [hy]

theorem source_energy_coercive_allp {p B : ℝ} (hp : 1<p) (hB : 0≤B)
    (A : ℝ) : ∃ R : ℝ,0≤R ∧ ∀ t : ℝ,R≤t → A<t^p/p-B*t := by
  have hp0 : 0<p := zero_lt_one.trans hp
  let S : ℝ := (2*B)^(p/(p-1))/(p/(p-1))
  have hlarge : ∀ᶠ t : ℝ in atTop,p*(2*A+S)<t^p :=
    (_root_.tendsto_rpow_atTop hp0).eventually (eventually_gt_atTop (p*(2*A+S)))
  obtain ⟨R,hR⟩ := eventually_atTop.mp hlarge
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro t ht
  have ht0 : 0≤t := (le_max_right R 0).trans ht
  have htR : R≤t := (le_max_left R 0).trans ht
  have hh : 2*A+S<t^p/p := (lt_div_iff₀ hp0).mpr
    (by simpa only [mul_comm] using hR t htR)
  have hy := Real.young_inequality_of_nonneg ht0
    (mul_nonneg (by norm_num : (0 : ℝ)≤2) hB)
    (Real.HolderConjugate.conjExponent hp)
  change t*(2*B)≤t^p/p+S at hy
  linarith only [hy,hh]

end BMCompactPDE
#print axioms BMCompactPDE.source_energy_bounded_below_allp
#print axioms BMCompactPDE.source_energy_coercive_allp

end
end ForcingSegmentForcingCoercivityAll

section ForcingSegmentForcingStability
/- Authored source: ForcingStability.lean; exact SHA256 07155e4d364d4f7288f6fa112f825b871e0b698c1fba3925b2c976876d83b783. -/

/-! Actual global source identities and uniqueness for common W0 data.
These results do not assert existence of a forced solution or regularity of
its representative. The test is constructed from the actual boundary pair. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.flux_difference_integral
    {n : ℕ} {p c d : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p d Ω v h)
    (hΩb : Bornology.IsBounded Ω)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h)) :
    Integrable (fun x=>inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))
      (volume.restrict Ω) ∧
    (∫ x in Ω,inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))=
      (c-d)*∫ x in Ω,u x-v x := by
  obtain ⟨hgi,_,hge⟩ := hu.integral_eq_global hΩb hSu hboundary
  obtain ⟨hhi,_,hhe⟩ := hv.integral_eq_global hΩb hSv hboundary
  have he : (fun x=>inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x))=
      fluxPairing p g (g-h)-fluxPairing p h (g-h) := by
    funext x
    simp only [fluxPairing,Pi.sub_apply,inner_sub_left]
  refine ⟨?_,?_⟩
  · rw [he]
    exact hgi.sub hhi
  · rw [he]
    change (∫ x in Ω,fluxPairing p g (g-h) x-fluxPairing p h (g-h) x)=
      (c-d)*∫ x in Ω,u x-v x
    rw [integral_sub hgi hhi,hge,hhe]
    simp only [Pi.sub_apply]
    ring

theorem WeakPSourcePair.gradient_ae_eq_of_same_source_W0
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hΩb : Bornology.IsBounded Ω)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h)) :
    g =ᵐ[volume.restrict Ω] h := by
  obtain ⟨hi,he⟩ := hu.flux_difference_integral hv hΩb hSu hSv hboundary
  have hnonneg : ∀ᵐ x ∂volume.restrict Ω,
      0 ≤ inner ℝ (pFlux p (g x)-pFlux p (h x)) (g x-h x) :=
    Eventually.of_forall (fun x=>pFlux_monotonicity hu.1 (g x) (h x))
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp
    (by simpa only [sub_self,zero_mul] using he)
  filter_upwards [hzero] with x hx
  exact (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).mp hx

theorem WeakPSourcePair.ae_eq_of_same_source_W0
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p c Ω v h)
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h)) :
    u =ᵐ[volume.restrict Ω] v := by
  have hg := hu.gradient_ae_eq_of_same_source_W0 hv hΩb hSu hSv hboundary
  have hdiff : g-h =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hg] with x hx
    simp only [Pi.sub_apply,hx,sub_self,Pi.zero_apply]
  have hz := hboundary.ae_eq_zero_of_gradient_ae_zero hn hu.2.1 hΩb hdiff
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

theorem WeakPSourcePair.ae_eq_of_common_boundary_data
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f u v : Space n → ℝ} {gf g h : Space n → Space n}
    (hf : SobolevPair p Ω f gf)
    (hu : WeakPSourcePair p c Ω (f+u) (gf+g))
    (hv : WeakPSourcePair p c Ω (f+v) (gf+h))
    (hbu : ZeroBoundarySobolevPair p Ω u g)
    (hbv : ZeroBoundarySobolevPair p Ω v h)
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    f+u =ᵐ[volume.restrict Ω] f+v := by
  apply hu.ae_eq_of_same_source_W0 hv hn hΩb (hf.add hbu.1) (hf.add hbv.1)
  have hw := hbu.sub_actual hbv
  apply hw.congr (Eventually.of_forall (fun x=>?_))
    (Eventually.of_forall (fun x=>?_))
  · simp only [Pi.add_apply,Pi.sub_apply]
    ring
  · simp only [Pi.add_apply,Pi.sub_apply]
    abel

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.flux_difference_integral
#print axioms BMCompactPDE.WeakPSourcePair.gradient_ae_eq_of_same_source_W0
#print axioms BMCompactPDE.WeakPSourcePair.ae_eq_of_same_source_W0
#print axioms BMCompactPDE.WeakPSourcePair.ae_eq_of_common_boundary_data

end
end ForcingSegmentForcingStability

section ForcingSegmentForcingOrder
/- Authored source: ForcingOrder.lean; exact SHA256 adf8961e28c01e23b5b7c7471ec467d9e4f1d0754942f7c5149a7d59393692b5. -/

/-! Forcing is monotone for actual Dirichlet weak solutions with the same
zero-boundary data. The positive-part W0 test is constructed from the genuine
W0 difference; no representative continuity or pointwise comparison premise
is supplied. The conclusion is correctly almost-everywhere. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.ae_le_of_ordered_source_W0
    {n : ℕ} {p c d : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p d Ω v h)
    (hcd : c≤d) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hSu : SobolevPair p Ω u g) (hSv : SobolevPair p Ω v h)
    (hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h)) :
    ∀ᵐ x ∂volume.restrict Ω,u x≤v x := by
  let θ : Space n → ℝ := fun x=>max (u x-v x) 0
  let w : Space n → Space n := fun x=>if 0<u x-v x then g x-h x else 0
  have hθ : ZeroBoundarySobolevPair p Ω θ w := hboundary.positivePart
  obtain ⟨hgi,hθi,hge⟩ := hu.integral_eq_global hΩb hSu hθ
  obtain ⟨hhi,_,hhe⟩ := hv.integral_eq_global hΩb hSv hθ
  let P : Space n → ℝ := fun x=>inner ℝ (pFlux p (g x)-pFlux p (h x)) (w x)
  have he : P=fluxPairing p g w-fluxPairing p h w := by
    funext x
    simp only [P,fluxPairing,Pi.sub_apply,inner_sub_left]
  have hPi : Integrable P (volume.restrict Ω) := by rw [he];exact hgi.sub hhi
  have hPnonneg : ∀ᵐ x ∂volume.restrict Ω,0≤P x := by
    apply Eventually.of_forall
    intro x
    by_cases hx : 0<u x-v x
    · simp only [P,w,if_pos hx]
      exact pFlux_monotonicity hu.1 (g x) (h x)
    · simp only [P,w,if_neg hx,inner_zero_right,le_refl]
  have hθnonneg : 0≤∫ x in Ω,θ x :=
    integral_nonneg (fun x=>le_max_right (u x-v x) 0)
  have hPnonpos : (∫ x in Ω,P x)≤0 := by
    rw [he]
    change (∫ x in Ω,fluxPairing p g w x-fluxPairing p h w x)≤0
    rw [integral_sub hgi hhi,hge,hhe]
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcd) hθnonneg]
  have hPzero : (∫ x in Ω,P x)=0 :=
    le_antisymm hPnonpos (integral_nonneg_of_ae hPnonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hPnonneg hPi).mp hPzero
  have hw : w =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hzero] with x hx
    by_cases hpos : 0<u x-v x
    · have hgh := (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).mp
        (by simpa only [P,w,if_pos hpos,Pi.zero_apply] using hx)
      simp only [w,if_pos hpos,hgh,sub_self,Pi.zero_apply]
    · simp only [w,if_neg hpos,Pi.zero_apply]
  have hθzero := hθ.ae_eq_zero_of_gradient_ae_zero hn hu.2.1 hΩb hw
  filter_upwards [hθzero] with x hx
  have hm : u x-v x≤0 := (le_max_left _ _).trans (by simpa only [θ,Pi.zero_apply] using hx.le)
  exact sub_nonpos.mp hm

theorem WeakPSourcePair.ae_le_of_ordered_source_common_data
    {n : ℕ} {p c d : ℝ} {Ω : Set (Space n)}
    {f u v : Space n → ℝ} {gf g h : Space n → Space n}
    (hf : SobolevPair p Ω f gf)
    (hu : WeakPSourcePair p c Ω (f+u) (gf+g))
    (hv : WeakPSourcePair p d Ω (f+v) (gf+h))
    (hbu : ZeroBoundarySobolevPair p Ω u g)
    (hbv : ZeroBoundarySobolevPair p Ω v h)
    (hcd : c≤d) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∀ᵐ x ∂volume.restrict Ω,(f+u) x≤(f+v) x := by
  apply hu.ae_le_of_ordered_source_W0 hv hcd hn hΩb (hf.add hbu.1) (hf.add hbv.1)
  have hw := hbu.sub_actual hbv
  apply hw.congr (Eventually.of_forall (fun x=>?_))
    (Eventually.of_forall (fun x=>?_))
  · simp only [Pi.add_apply,Pi.sub_apply]
    ring
  · simp only [Pi.add_apply,Pi.sub_apply]
    abel

theorem WeakPHarmonicPair.source_zero {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) : WeakPSourcePair p 0 Ω u g := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro D hD θ h hθ
  obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi,by simpa only [zero_mul] using he⟩

theorem WeakPSourcePair.harmonic_of_source_zero {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p 0 Ω u g) : WeakPHarmonicPair p Ω u g := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro D hD θ h hθ
  obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi,by simpa only [zero_mul] using he⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.ae_le_of_ordered_source_W0
#print axioms BMCompactPDE.WeakPSourcePair.ae_le_of_ordered_source_common_data
#print axioms BMCompactPDE.WeakPHarmonicPair.source_zero
#print axioms BMCompactPDE.WeakPSourcePair.harmonic_of_source_zero

end
end ForcingSegmentForcingOrder

section ForcingSegmentForcingEnergy
/- Authored source: ForcingEnergy.lean; exact SHA256 1bb81cbed0ade901d1fdc1a1d81d550bd2dadd232c319073bd9d81fdaaf9bcf7. -/

/-! Genuine global forced energy inequalities from the actual source equation.
The source equation is used with constructed full-W0 perturbations; neither a
minimizer nor an energy inequality is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.energy_tangent_global
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hΩb : Bornology.IsBounded Ω)
    (hSob : SobolevPair p Ω u g)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ h) :
    (∫ x in Ω,‖g x‖^p)+p*c*(∫ x in Ω,θ x) ≤
      ∫ x in Ω,‖g x+h x‖^p := by
  have hi := integrable_norm_rpow_of_memLp hu.1 hSob.2.2.1
  have hj := integrable_norm_rpow_of_memLp hu.1 (hSob.2.2.1.add hθ.1.2.2.1)
  obtain ⟨hpair,_,he⟩ := hu.integral_eq_global hΩb hSob hθ
  have hle := integral_mono (hi.add (hpair.const_mul p)) hj
    (fun x=>norm_rpow_add_tangent_lower hu.1 (g x) (h x))
  simp only [Pi.add_apply] at hle
  rw [integral_add hi (hpair.const_mul p),integral_const_mul,he] at hle
  simpa only [mul_assoc] using hle

theorem WeakPSourcePair.energy_le_boundary_energy_add_load
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f w : Space n → ℝ} {gf gw : Space n → Space n}
    (hf : SobolevPair p Ω f gf)
    (hu : WeakPSourcePair p c Ω (f+w) (gf+gw))
    (hw : ZeroBoundarySobolevPair p Ω w gw)
    (hΩb : Bornology.IsBounded Ω) :
    (∫ x in Ω,‖gf x+gw x‖^p) ≤
      (∫ x in Ω,‖gf x‖^p)+p*c*(∫ x in Ω,w x) := by
  have hs := hu.energy_tangent_global hΩb (hf.add hw.1) (hw.smul_actual (-1))
  have hvec (x : Space n) : (gf+gw) x+((-1 : ℝ) • gw) x=gf x := by
    simp only [Pi.add_apply,Pi.smul_apply,neg_one_smul]
    abel
  have hfun : ((-1 : ℝ) • w)=-w := neg_one_smul ℝ w
  simp_rw [hvec] at hs
  rw [hfun] at hs
  simp only [Pi.neg_apply] at hs
  rw [integral_neg] at hs
  simp only [Pi.add_apply] at hs
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.energy_tangent_global
#print axioms BMCompactPDE.WeakPSourcePair.energy_le_boundary_energy_add_load

end
end ForcingSegmentForcingEnergy

section ForcingSegmentForcingEulerDensity
/- Authored source: ForcingEulerDensity.lean; exact SHA256 216e89ee07af007200b770994f6f727827082fdd467dee38edbf76d3b08b373c. -/

/-! Smooth Euler equations yield the actual full-W0 source predicate.
The full equation for rough tests is derived by both actual graph limits;
there is no zero-extension or global-testing premise for a rough test. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

private theorem source_integral_eq_of_smooth_tests
    {n : ℕ} {p c : ℝ} (hp : 1<p) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict D))
    (hsmooth : ∀ φ : Space n → ℝ,SmoothTest D φ →
      (∫ x in D,fluxPairing p g (gradient φ) x)=c*∫ x in D,φ x)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p D θ h) :
    Integrable (fluxPairing p g h) (volume.restrict D) ∧
      (∫ x in D,fluxPairing p g h x)=c*∫ x in D,θ x := by
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  haveI := holderConjugate_p_dual hp
  have hF := memLp_pFlux hp hg
  have hi := inner_integrable_of_dual_memLp hF hθ.1.2.2.1
  obtain ⟨hs,φ,hφ,hLu,hLg⟩ := hθ
  have hφs (j : ℕ) := (hφ j).sobolevPair hp
  have htF := tendsto_integral_inner_of_eLpNorm_sub_zero hF hs.2.2.1
    (fun j=>(hφs j).2.2.1) hLg
  have hOne : MemLp (fun _ : Space n => (1 : ℝ))
      (ENNReal.ofReal (p/(p-1))) (volume.restrict D) := memLp_const 1
  have htθ : Tendsto (fun j=>∫ x in D,φ j x) atTop (𝓝 (∫ x in D,θ x)) := by
    simpa only [Real.inner_apply,one_mul] using
      tendsto_integral_inner_of_eLpNorm_sub_zero hOne hs.2.1
        (fun j=>(hφs j).2.1) hLu
  refine ⟨hi,?_⟩
  exact tendsto_nhds_unique htF
    ((htθ.const_mul c).congr' (Eventually.of_forall
      (fun j=>(hsmooth (φ j) (hφ j)).symm)))

theorem weakPSourcePair_of_sobolev_smooth_source_equation
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g)
    (he : ∀ φ : Space n → ℝ,SmoothTest Ω φ →
      (∫ x in Ω,fluxPairing p g (gradient φ) x)=c*∫ x in Ω,φ x) :
    WeakPSourcePair p c Ω u g := by
  refine ⟨hu.1,hΩ,hu.locally_actual,?_⟩
  intro D hD θ h hθ
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  apply source_integral_eq_of_smooth_tests hu.1 hD.2.1
    (hu.mono_actual hDΩ).2.2.1 ?_ hθ
  intro φ hφ
  have ht : SmoothTest Ω φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hDΩ⟩
  have hzero (x : Space n) (hx : x∉D) : φ x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h=>hx (hφ.2.2 h))
  have hgzero (x : Space n) (hx : x∉D) : gradient φ x=0 :=
    BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun h=>hx (hφ.2.2 h))
  have hI (S : Set (Space n)) (hDS : D⊆S) :
      (∫ x in S,fluxPairing p g (gradient φ) x)=∫ x,fluxPairing p g (gradient φ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by
      simp only [fluxPairing,hgzero x (fun h=>hx (hDS h)),inner_zero_right])
  have hJ (S : Set (Space n)) (hDS : D⊆S) : (∫ x in S,φ x)=∫ x,φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>hzero x (fun h=>hx (hDS h)))
  have heφ := he φ ht
  rw [hI Ω hDΩ,hJ Ω hDΩ] at heφ
  rw [hI D Subset.rfl,hJ D Subset.rfl]
  exact heφ

end BMCompactPDE
#print axioms BMCompactPDE.weakPSourcePair_of_sobolev_smooth_source_equation

end
end ForcingSegmentForcingEulerDensity

section ForcingSegmentForcingUniformEnergy
/- Authored source: ForcingUniformEnergy.lean; exact SHA256 11d1e6550a1b501782ce84d0422ad272f34cfa9e2f0ddfb6c5d5ff23d319cff5. -/

/-! Genuine uniform source-gradient bounds for every 1<p<n. The ordinary
source is bounded by C, but no solution-energy or norm bound is a premise.
Young coercivity absorbs the actual load, controlled by proved Poincare. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

private theorem raw_energy_eq_lp_power
    {n : ℕ} {p : ℝ} (hp : 1<p) {μ : Measure (Space n)}
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=‖hg.toLp g‖^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he := integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun v=>‖v‖^p))
  exact he.symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral
    (zero_lt_one.trans hp) (hg.toLp g)).symm

theorem exists_uniform_forced_gradient_bound
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) (hpn : p<(n : ℝ))
    (hΩb : Bornology.IsBounded Ω) {C : ℝ} (hC : 0≤C) :
    ∃ R : ℝ,0≤R ∧ ∀ {c : ℝ} {w : Space n → ℝ} {gw : Space n → Space n},
      |c|≤C → ZeroBoundarySobolevPair p Ω w gw →
      WeakPSourcePair p c Ω (f+w) (gf+gw) →
      (eLpNorm (gf+gw) (ENNReal.ofReal p) (volume.restrict Ω)).toReal≤R := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  have hp0 : 0<p := zero_lt_one.trans hf.1
  obtain ⟨K,hK,hload⟩ := exists_W0_source_load_bound hf.1 hpn hΩb
  let μ := volume.restrict Ω
  let F := hf.2.2.1.toLp gf
  let B : ℝ := ‖F‖
  let M : ℝ := B^p/p+C*K*B
  obtain ⟨R,hR0,hR⟩ := source_energy_coercive_allp hf.1 (mul_nonneg hC hK) M
  refine ⟨R,hR0,?_⟩
  intro c w gw hc hw hu
  let G := hw.1.2.2.1.toLp gw
  let A : ℝ := ‖F+G‖
  have hG : ‖G‖≤A+B := by
    calc
      ‖G‖=‖(F+G)-F‖ := by congr 1;abel
      _≤‖F+G‖+‖F‖ := norm_sub_le _ _
  have hload' : |∫ x in Ω,w x|≤K*‖G‖ := by
    simpa only [G,Lp.norm_toLp] using hload hw
  have hci : c*(∫ x in Ω,w x)≤C*K*‖G‖ := by
    calc
      c*(∫ x in Ω,w x)≤|c| * |∫ x in Ω,w x| := by
        simpa only [abs_mul] using le_abs_self (c*(∫ x in Ω,w x))
      _≤C*(K*‖G‖) := mul_le_mul hc hload' (abs_nonneg _) hC
      _=C*K*‖G‖ := by ring
  have hci' : c*(∫ x in Ω,w x)≤C*K*(A+B) :=
    hci.trans (mul_le_mul_of_nonneg_left hG (mul_nonneg hC hK))
  have hEC : (∫ x in Ω,‖gf x+gw x‖^p)=A^p := by
    change (∫ x in Ω,‖(gf+gw) x‖^p)=A^p
    rw [raw_energy_eq_lp_power hf.1 (hf.2.2.1.add hw.1.2.2.1),
      MemLp.toLp_add hf.2.2.1 hw.1.2.2.1]
  have hEF : (∫ x in Ω,‖gf x‖^p)=B^p := raw_energy_eq_lp_power hf.1 hf.2.2.1
  have he := WeakPSourcePair.energy_le_boundary_energy_add_load hf hu hw hΩb
  rw [hEC,hEF] at he
  have hsource : A^p≤B^p+p*(C*K*(A+B)) := by
    have hh := mul_le_mul_of_nonneg_left hci' hp0.le
    nlinarith only [he,hh]
  have hupper : A^p/p-C*K*A≤M := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp0).mpr
    have hright : (M+C*K*A)*p=B^p+p*(C*K*(A+B)) := by
      dsimp only [M]
      field_simp [hp0.ne']
      ring
    rw [hright]
    exact hsource
  have heq : (eLpNorm (gf+gw) (ENNReal.ofReal p) (volume.restrict Ω)).toReal=A := by
    rw [←Lp.norm_toLp (gf+gw) (hf.2.2.1.add hw.1.2.2.1),
      MemLp.toLp_add hf.2.2.1 hw.1.2.2.1]
  rw [heq]
  by_contra hnot
  exact (hR A (lt_of_not_ge hnot).le).not_ge hupper

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_forced_gradient_bound

end
end ForcingSegmentForcingUniformEnergy

end AnalyticBlock_ForcingPreExistenceBatch

section AnalyticBlock_NonlinearConstructionBatch
/- Exact prepared input: NonlinearConstructionBatch.lean; SHA256 f3c42eaba4e707bf9aa61f09ebc0265c7733aa2fb04d9abf5bb13e975aac9495. -/

/-! Prospective all-p nonlinear construction batch. The five readable segments
are composed and counted once; exact source/body hashes and line maps are in
NonlinearConstructionSegments.manifest.json. This generator performs no check. -/
set_option autoImplicit false

section NonlinearSegment_NonlinearEnergyDerivative

/-! The actual first variation of the integrated p-energy for arbitrary Lp fields.
The input fields have no classical differentiability assumption. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace α] {μ : Measure α}

theorem hasDerivAt_energy_line {p : ℝ} (hp : 1<p) (v h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖v+s • h‖^p)
      (p*inner ℝ (pFlux p (v+t • h)) h) t := by
  have hlin : HasDerivAt (fun s : ℝ => v+s • h) h t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const h).const_add v
  have hh := (hasFDerivAt_energy_norm hp (v+t • h)).comp_hasDerivAt t hlin
  convert! hh using 1 <;>
    simp only [Function.comp_def,id_eq,ContinuousLinearMap.smul_apply,innerSL_apply_apply,
      smul_eq_mul,pFlux,real_inner_smul_left,mul_assoc]

theorem energy_line_deriv_bound {p : ℝ} (hp : 1<p) (v h : E)
    {t : ℝ} (ht : |t|≤1) :
    ‖p*inner ℝ (pFlux p (v+t • h)) h‖ ≤ p*(‖v‖+‖h‖)^p := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hp1 : 0≤p-1 := by linarith
  have hnorm : ‖v+t • h‖ ≤ ‖v‖+‖h‖ := by
    calc
      ‖v+t • h‖ ≤ ‖v‖+‖t • h‖ := norm_add_le _ _
      _ = ‖v‖ + |t| * ‖h‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ ‖v‖+‖h‖ := by nlinarith [norm_nonneg h]
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hnorm hp1
  have hmul : ‖v+t • h‖^(p-1)*‖h‖ ≤ (‖v‖+‖h‖)^p := by
    calc
      _ ≤ (‖v‖+‖h‖)^(p-1)*‖h‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (‖v‖+‖h‖)^(p-1)*(‖v‖+‖h‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (Real.rpow_nonneg (by positivity) _)
      _ = (‖v‖+‖h‖)^p := by
        rw [← Real.rpow_add_one' (by positivity) (by linarith : p-1+1≠0)]
        congr 1
        ring
  calc
    _ = p * |inner ℝ (pFlux p (v+t • h)) h| := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos hp0]
    _ ≤ p*(‖pFlux p (v+t • h)‖*‖h‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hp0.le
    _ = p*(‖v+t • h‖^(p-1)*‖h‖) := by rw [norm_pFlux hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul hp0.le

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_integral_energy_line {p : ℝ} (hp : 1<p)
    {g h : α → E} (hg : MemLp g (ENNReal.ofReal p) μ)
    (hh : MemLp h (ENNReal.ofReal p) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, ‖g x+t • h x‖^p ∂μ)
      (p*(∫ x, inner ℝ (pFlux p (g x)) (h x) ∂μ)) 0 := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hq0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hi : Integrable (fun x => ‖g x‖^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hg.integrable_norm_rpow hq0 hqt
  have hs := hg.norm.add hh.norm
  have hb : Integrable (fun x => p*(‖g x‖+‖h x‖)^p) μ := by
    have hh' := (hs.integrable_norm_rpow hq0 hqt).const_mul p
    simpa only [ENNReal.toReal_ofReal hp0.le,Pi.add_apply,Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hh'
  have hm : AEStronglyMeasurable (fun x => p*inner ℝ (pFlux p (g x)) (h x)) μ :=
    (((continuous_pFlux hp).comp_aestronglyMeasurable hg.1).inner hh.1).const_mul p
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Metric.ball (0:ℝ) 1) (x₀ := (0:ℝ))
    (F := fun t x => ‖g x+t • h x‖^p)
    (F' := fun t x => p*inner ℝ (pFlux p (g x+t • h x)) (h x))
    (bound := fun x => p*(‖g x‖+‖h x‖)^p)
    (Metric.ball_mem_nhds 0 zero_lt_one)
    (Eventually.of_forall (fun t =>
      ((hg.1.add (hh.1.const_smul t)).norm.aemeasurable.pow_const p).aestronglyMeasurable))
    (by simpa only [zero_smul,add_zero] using hi)
    (by simpa only [zero_smul,add_zero] using hm)
    (Eventually.of_forall (fun x t ht => energy_line_deriv_bound hp (g x) (h x)
      (by
        have ht' : |t|<1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
        exact ht'.le))) hb
    (Eventually.of_forall (fun x t _ => hasDerivAt_energy_line hp (g x) (h x) t))
  simpa only [zero_smul,add_zero,integral_const_mul] using H.2

end BMCompactPDE

end -- original file noncomputable section
end NonlinearSegment_NonlinearEnergyDerivative

section NonlinearSegment_NonlinearLoad

/-! The actual integral load on the concrete W0 Lp graph. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal Topology
namespace BMCompactPDE

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1<p)

def w0LpLoadLinear {n : ℕ} {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    w0LpGraph p hp n Ω →ₗ[ℝ] ℝ := by
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let μ := volume.restrict Ω
  have hi (v : w0LpGraph p hp n Ω) : Integrable (v.1.1 : Space n → ℝ) μ :=
    (Lp.memLp v.1.1).integrable (Fact.out : 1≤ENNReal.ofReal p)
  exact
    { toFun := fun v => ∫ x, (v.1.1 : Space n → ℝ) x ∂μ
      map_add' := by
        intro v w
        change (∫ x, ((v.1.1+w.1.1 : ScalarLp p n Ω) : Space n → ℝ) x ∂μ) = _
        calc
          _ = ∫ x, (v.1.1 : Space n → ℝ) x+(w.1.1 : Space n → ℝ) x ∂μ :=
            integral_congr_ae (Lp.coeFn_add v.1.1 w.1.1)
          _ = _ := integral_add (hi v) (hi w)
      map_smul' := by
        intro c v
        change (∫ x, ((c • v.1.1 : ScalarLp p n Ω) : Space n → ℝ) x ∂μ) = _
        calc
          _ = ∫ x, c*(v.1.1 : Space n → ℝ) x ∂μ :=
            integral_congr_ae (Lp.coeFn_smul c v.1.1)
          _ = _ := by
            simpa only [RingHom.id_apply,smul_eq_mul] using
              (integral_const_mul c (v.1.1 : Space n → ℝ)) }

theorem w0LpLoadLinear_apply {n : ℕ} {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    (v : w0LpGraph p hp n Ω) :
    w0LpLoadLinear p hp hΩb v = ∫ x in Ω, (v.1.1 : Space n → ℝ) x := rfl

theorem exists_w0LpLoadCLM {n : ℕ} (hpn : p<(n:ℝ))
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0≤K ∧ ∃ L : w0LpGraph p hp n Ω →L[ℝ] ℝ,
      (∀ v, L v = ∫ x in Ω, (v.1.1 : Space n → ℝ) x) ∧
      ∀ v, |L v|≤K*‖v.1.2‖ := by
  obtain ⟨K,hK,hbound⟩ := exists_W0_source_load_bound hp hpn hΩb
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

end BMCompactPDE

end -- original file noncomputable section
end NonlinearSegment_NonlinearLoad

section NonlinearSegment_NonlinearEnergyMin

/-! A constructed actual nonlinear source-energy minimum, for every 1<p<n.
The concrete W0 graph, load and coercivity are proved rather than assumed. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal Topology
namespace BMCompactPDE
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1<p)

def w0LpSourceEnergy {n : ℕ} {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    (F : VectorLp p n Ω) (c : ℝ) (w : w0LpGraph p hp n Ω) : ℝ :=
  ‖F+w.1.2‖^p-p*c*(w0LpLoadLinear p hp hΩb w)

set_option maxHeartbeats 1000000 in
theorem exists_w0LpSourceEnergy_minimum {n : ℕ} (hpn : p<(n:ℝ))
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω)
    (F : VectorLp p n Ω) (c : ℝ) :
    ∃ v : w0LpGraph p hp n Ω, ∀ z : w0LpGraph p hp n Ω,
      w0LpSourceEnergy p hp hΩb F c v ≤ w0LpSourceEnergy p hp hΩb F c z := by
  have hp0 : 0<p := zero_lt_one.trans hp
  letI : CompleteSpace (w0LpGraph p hp n Ω) :=
    (isClosed_w0LpGraph p hp n Ω).completeSpace_coe
  obtain ⟨K,hK,L,hL,hload⟩ := exists_w0LpLoadCLM p hp hpn hΩb
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
  obtain ⟨A,hA⟩ := exists_w0LpGradient_antilipschitz p hp hpn hΩb
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

end BMCompactPDE

end -- original file noncomputable section
end NonlinearSegment_NonlinearEnergyMin

section NonlinearSegment_NonlinearEuler

/-! Actual Euler identity for an energy minimum, to be applied to a constructed
minimum. This intermediary does not assert that a minimum exists. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

theorem source_flux_identity_of_actual_energy_minimum {n : ℕ} {p c : ℝ}
    (hp : 1<p) {Ω : Set (Space n)} {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict Ω))
    (hmin : ∀ (θ : Space n → ℝ) (h : Space n → Space n),
      ZeroBoundarySobolevPair p Ω θ h →
      (∫ x in Ω, ‖g x‖^p) ≤
        (∫ x in Ω, ‖g x+h x‖^p)-p*c*(∫ x in Ω, θ x))
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ h) :
    Integrable (fun x => inner ℝ (pFlux p (g x)) (h x)) (volume.restrict Ω) ∧
      (∫ x in Ω, inner ℝ (pFlux p (g x)) (h x)) = c*(∫ x in Ω, θ x) := by
  let μ := volume.restrict Ω
  let I : ℝ := ∫ x, inner ℝ (pFlux p (g x)) (h x) ∂μ
  let T : ℝ := ∫ x, θ x ∂μ
  let F : ℝ → ℝ := fun t => (∫ x, ‖g x+t • h x‖^p ∂μ)-p*c*(t*T)
  have hlocal : IsLocalMin F 0 := by
    apply Eventually.of_forall
    intro t
    have ht := hmin (t • θ) (t • h) (hθ.smul_actual t)
    simpa only [F,T,μ,Pi.smul_apply,smul_eq_mul,integral_const_mul,
      zero_smul,add_zero,zero_mul,mul_zero,sub_zero] using ht
  have hd : HasDerivAt F (p*I-p*c*T) 0 := by
    convert! (hasDerivAt_integral_energy_line hp hg hθ.1.2.2.1).sub
      (((hasDerivAt_id (0:ℝ)).mul_const T).const_mul (p*c)) using 1 <;>
        simp only [F,I,μ,Pi.sub_apply,one_mul,id_eq]
  have hz := hlocal.hasDerivAt_eq_zero hd
  have hz' : p*(I-c*T)=0 := by nlinarith [hz]
  have hI : I=c*T := sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (zero_lt_one.trans hp).ne')
  letI : ENNReal.HolderConjugate (ENNReal.ofReal (p/(p-1))) (ENNReal.ofReal p) :=
    holderConjugate_p_dual hp
  refine ⟨inner_integrable_of_memLp (memLp_pFlux hp hg) hθ.1.2.2.1,hI⟩

end BMCompactPDE

end -- original file noncomputable section
end NonlinearSegment_NonlinearEuler

section NonlinearSegment_NonlinearDirichlet

/-! Actual nonlinear Dirichlet and constant-source existence, 1<p<n.
All W0 graph and energy-minimum objects are constructed from the actual data. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

theorem ZeroBoundarySobolevPair.exists_w0LpGraph_representatives
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1<p)
    {n : ℕ} {Ω : Set (Space n)} {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ h) :
    ∃ z : w0LpGraph p hp n Ω,
      (z.1.1 : Space n → ℝ) =ᵐ[volume.restrict Ω] θ ∧
      (z.1.2 : Space n → Space n) =ᵐ[volume.restrict Ω] h := by
  let S := hθ.1.2.1.toLp θ
  let H := hθ.1.2.2.1.toLp h
  have hz : ZeroBoundarySobolevPair p Ω (S : Space n → ℝ) (H : Space n → Space n) :=
    hθ.congr (MemLp.coeFn_toLp hθ.1.2.1).symm (MemLp.coeFn_toLp hθ.1.2.2.1).symm
  exact ⟨⟨(S,H),hz⟩,MemLp.coeFn_toLp hθ.1.2.1,MemLp.coeFn_toLp hθ.1.2.2.1⟩

set_option maxHeartbeats 1000000 in
theorem exists_weak_source_Dirichlet {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n:ℝ)) {Ω : Set (Space n)}
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
  obtain ⟨v,hv⟩ := exists_w0LpSourceEnergy_minimum p hp hpn hΩb F c
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

theorem exists_weak_harmonic_Dirichlet {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n:ℝ)) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ w : Space n → ℝ, ∃ gw : Space n → Space n,
      ZeroBoundarySobolevPair p Ω w gw ∧
      WeakPHarmonicPair p Ω (f+w) (gf+gw) := by
  obtain ⟨w,gw,hw,hsol⟩ := exists_weak_source_Dirichlet hp hpn hΩ hΩb 0 hf
  exact ⟨w,gw,hw,hsol.harmonic_of_source_zero⟩

end BMCompactPDE

end -- original file noncomputable section
end NonlinearSegment_NonlinearDirichlet

#print axioms BMCompactPDE.hasDerivAt_energy_line
#print axioms BMCompactPDE.energy_line_deriv_bound
#print axioms BMCompactPDE.hasDerivAt_integral_energy_line
#print axioms BMCompactPDE.w0LpLoadLinear_apply
#print axioms BMCompactPDE.exists_w0LpLoadCLM
#print axioms BMCompactPDE.exists_w0LpSourceEnergy_minimum
#print axioms BMCompactPDE.source_flux_identity_of_actual_energy_minimum
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.exists_w0LpGraph_representatives
#print axioms BMCompactPDE.exists_weak_source_Dirichlet
#print axioms BMCompactPDE.exists_weak_harmonic_Dirichlet

end AnalyticBlock_NonlinearConstructionBatch

section AnalyticBlock_ForcingFamilyBatch
/- Exact prepared input: ForcingFamilyBatch.lean; SHA256 feda00a9f1719c239376e16794c089c3fcf3b2fe39a601e7ed9af5b412fef66b. -/

/-! PROSPECTIVE EXACT-BODY BATCH: uncounted until native PASS.
Original authored sources, individual body hashes and import mapping are in ForcingBatches/.
Each retained source body is byte-for-byte unchanged; only import hoisting and explicit EOF section closure are added. -/

section ForcingSegmentForcingConvergenceAllp
/- Authored source: ForcingConvergenceAllp.lean; exact SHA256 25b7069edb097c73581766edc0756ac3ff890f8933cd58533d81d3cb6b6f2511. -/

/-! Strong actual W1,p stability for every 1<p<n. The only convergence input
is scalar forcing tending to zero. Source norm bounds are derived by Young
coercivity; genuine harmonic midpoint minimality and the proved bounded-Lp
midpoint gap then force strong gradient convergence. No selected pointwise
representative or family-existence conclusion is asserted by this estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

private theorem family_energy_eq_lp_power
    {n : ℕ} {p : ℝ} (hp : 1<p) {μ : Measure (Space n)}
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=‖hg.toLp g‖^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he := integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun v=>‖v‖^p))
  exact he.symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral
    (zero_lt_one.trans hp) (hg.toLp g)).symm

private theorem harmonic_lp_midpoint_minimum
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f w : Space n → ℝ} {gf gw : Space n → Space n}
    (hH : WeakPHarmonicPair p Ω f gf) (hf : SobolevPair p Ω f gf)
    (hw : ZeroBoundarySobolevPair p Ω w gw) (hΩb : Bornology.IsBounded Ω) :
    ‖hf.2.2.1.toLp gf‖^p ≤
      ‖(1/2 : ℝ) • ((hf.2.2.1.toLp gf+hw.1.2.2.1.toLp gw)+hf.2.2.1.toLp gf)‖^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  have hm := hH.source_zero.energy_tangent_global hΩb hf (hw.smul_actual (1/2 : ℝ))
  simp only [mul_zero,zero_mul,add_zero] at hm
  change (∫ x in Ω,‖gf x‖^p)≤∫ x in Ω,‖(gf+(1/2 : ℝ) • gw) x‖^p at hm
  rw [family_energy_eq_lp_power hf.1 hf.2.2.1,
    family_energy_eq_lp_power hf.1 (hf.2.2.1.add (hw.1.2.2.1.const_smul (1/2 : ℝ))),
    MemLp.toLp_add hf.2.2.1 (hw.1.2.2.1.const_smul (1/2 : ℝ)),
    MemLp.toLp_const_smul (1/2 : ℝ) hw.1.2.2.1] at hm
  have hvec : hf.2.2.1.toLp gf+(1/2 : ℝ) • hw.1.2.2.1.toLp gw=
      (1/2 : ℝ) • ((hf.2.2.1.toLp gf+hw.1.2.2.1.toLp gw)+hf.2.2.1.toLp gf) := by module
  simpa only [hvec] using hm

theorem WeakPHarmonicPair.forced_family_W1p_tendsto_allp
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPHarmonicPair p Ω f gf) (hf : SobolevPair p Ω f gf)
    (hpn : p<(n : ℝ)) (hΩb : Bornology.IsBounded Ω)
    {c : ℕ → ℝ} {w : ℕ → Space n → ℝ} {gw : ℕ → Space n → Space n}
    (hw : ∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j))
    (hu : ∀ j,WeakPSourcePair p (c j) Ω (f+w j) (gf+gw j))
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω))
      atTop (𝓝 0) ∧
    Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω))
      atTop (𝓝 0) := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  have hp0 : 0<p := zero_lt_one.trans hf.1
  obtain ⟨C,hC,hCb⟩ := (Metric.isBounded_range_of_tendsto c hc).exists_pos_norm_le
  have hCj (j : ℕ) : |c j|≤C := by
    simpa only [Real.norm_eq_abs] using hCb (c j) (mem_range_self j)
  obtain ⟨R,hR0,hR⟩ := exists_uniform_forced_gradient_bound hf hpn hΩb hC.le
  obtain ⟨K,hK,hload⟩ := exists_W0_source_load_bound hf.1 hpn hΩb
  let F := hf.2.2.1.toLp gf
  let G (j : ℕ) := (hw j).1.2.2.1.toLp (gw j)
  let A (j : ℕ) := F+G j
  let M : ℝ := K*(R+‖F‖)
  have hAj (j : ℕ) : ‖A j‖≤R := by
    dsimp only [A,F,G]
    rw [←MemLp.toLp_add hf.2.2.1 (hw j).1.2.2.1,Lp.norm_toLp]
    exact hR (hCj j) (hw j) (hu j)
  have hGj (j : ℕ) : ‖G j‖≤R+‖F‖ := by
    have hdiff : G j=A j-F := by dsimp only [A];abel
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add (hAj j) le_rfl)
  have hIj (j : ℕ) : |∫ x in Ω,w j x|≤M := by
    have he : |∫ x in Ω,w j x|≤K*‖G j‖ := by
      simpa only [G,Lp.norm_toLp] using hload (hw j)
    exact he.trans (mul_le_mul_of_nonneg_left (hGj j) hK)
  have hnormal : Tendsto (fun j=>‖G j‖) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let S := max R ‖F‖
    obtain ⟨κ,hκ,hgap⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (α := Space n) (μ := volume.restrict Ω) hf.1 S ε hε
    have hsmalllim : Tendsto (fun j=>(p*M/2)*|c j|) atTop (𝓝 0) := by
      simpa only [abs_zero,mul_zero] using hc.abs.const_mul (p*M/2)
    have hsmall : ∀ᶠ j in atTop,(p*M/2)*|c j|<κ :=
      (tendsto_order.mp hsmalllim).2 κ hκ
    filter_upwards [hsmall] with j hj
    have hlt : ‖G j‖<ε := by
      by_contra hnot
      have hdiff : A j-F=G j := by dsimp only [A];abel
      have hsep : ε≤‖A j-F‖ := by rw [hdiff];exact le_of_not_gt hnot
      have hg := hgap (A j) F ((hAj j).trans (le_max_left _ _)) (le_max_right _ _) hsep
      have hm := harmonic_lp_midpoint_minimum hH hf (hw j) hΩb
      have he := WeakPSourcePair.energy_le_boundary_energy_add_load hf (hu j) (hw j) hΩb
      change ‖F‖^p≤‖(1/2 : ℝ) • (A j+F)‖^p at hm
      have hEC : (∫ x in Ω,‖gf x+gw j x‖^p)=‖A j‖^p := by
        change (∫ x in Ω,‖(gf+gw j) x‖^p)=‖A j‖^p
        rw [family_energy_eq_lp_power hf.1 (hf.2.2.1.add (hw j).1.2.2.1),
          MemLp.toLp_add hf.2.2.1 (hw j).1.2.2.1]
      have hEF : (∫ x in Ω,‖gf x‖^p)=‖F‖^p := family_energy_eq_lp_power hf.1 hf.2.2.1
      rw [hEC,hEF] at he
      have hci : c j*(∫ x in Ω,w j x)≤|c j| * M := by
        calc
          c j*(∫ x in Ω,w j x)≤|c j| * |∫ x in Ω,w j x| := by
            simpa only [abs_mul] using le_abs_self (c j*(∫ x in Ω,w j x))
          _≤|c j| * M := mul_le_mul_of_nonneg_left (hIj j) (abs_nonneg _)
      have hupper : ‖A j‖^p≤‖F‖^p+p*|c j| * M := by
        have hh := mul_le_mul_of_nonneg_left hci hp0.le
        nlinarith only [he,hh]
      nlinarith only [hg,hm,hupper,hj]
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)] using hlt
  have hg : Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω))
      atTop (𝓝 0) := by
    have hr : Tendsto (fun j=>(eLpNorm (gw j) (ENNReal.ofReal p)
        (volume.restrict Ω)).toReal) atTop (𝓝 0) := by
      simpa only [G,Lp.norm_toLp] using hnormal
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    funext j
    exact (ENNReal.ofReal_toReal (hw j).1.2.2.1.eLpNorm_ne_top).symm
  obtain ⟨P,hP⟩ := exists_W0_Lp_poincare_constant hf.1 hpn hΩb
  have hupper : Tendsto (fun j=>(P : ℝ≥0∞)*eLpNorm (gw j) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr ENNReal.coe_ne_top)
  exact ⟨hg,tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _=>bot_le) (fun j=>hP (hw j))⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.forced_family_W1p_tendsto_allp

end
end ForcingSegmentForcingConvergenceAllp

section ForcingSegmentForcingFamily
/- Authored source: ForcingFamily.lean; exact SHA256 9f4056cde17c23da18ac559e66a5834f8ba3da66e7f2c6d4b9c9af4b400a61a0. -/

/-! A genuinely constructed positive-source approximating family, 1<p<n.
The existence theorem is a proved dependency, not an existence premise.
The resulting convergence is strong W1,p of the actual Sobolev corrections;
continuous/C1 representatives and selected pointwise convergence are not
claimed by this construction. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

theorem WeakPHarmonicPair.exists_forced_W1p_approximants
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPHarmonicPair p Ω f gf) (hf : SobolevPair p Ω f gf)
    (hpn : p<(n : ℝ)) (hΩb : Bornology.IsBounded Ω) :
    ∃ w : ℕ → Space n → ℝ,∃ gw : ℕ → Space n → Space n,
      (∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j)) ∧
      (∀ j : ℕ,WeakPSourcePair p (((j : ℝ)+1)⁻¹) Ω (f+w j) (gf+gw j)) ∧
      (∀ j : ℕ,0<((j : ℝ)+1)⁻¹) ∧
      Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (𝓝 0) := by
  have hex (j : ℕ) := exists_weak_source_Dirichlet hf.1 hpn hH.2.1 hΩb
    (((j : ℝ)+1)⁻¹) hf
  choose w gw hw hu using hex
  have hc : Tendsto (fun j : ℕ=>((j : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  obtain ⟨hg,hwlim⟩ := hH.forced_family_W1p_tendsto_allp hf hpn hΩb hw hu hc
  exact ⟨w,gw,hw,hu,fun j=>inv_pos.mpr (by positivity),hg,hwlim⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_forced_W1p_approximants

end
end ForcingSegmentForcingFamily

end AnalyticBlock_ForcingFamilyBatch

section AnalyticBlock_RegularityBoundedBatch
/- Exact prepared input: scouting/RegularityBoundedBatch.lean; SHA256 b5e5b5bd4cfb9bcca3e4898088090c0b3fce385c5260a6cebcc0e6fa51364087. -/

/-! Prospective source-only batch of four remaining regularity statements.
Prepared only; no native verdict or proof count is inferred from this export. -/

/- Body retained from RegularityDecay.lean; see the adjacent exact provenance map. -/
noncomputable section RegularityBody_RegularityDecay

/-! Discrete decay used by the actual weak-solution weighted tail iteration.
This numerical lemma alone is not a regularity theorem. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace BMCompactPDE

theorem regularity_superlinear_decay {A B α : ℝ}
    (hA : 0<A) (hB : 1≤B) (hα : 0<α) :
    ∃ ε : ℝ, 0<ε ∧ ∀ X : ℕ → ℝ,
      (∀ j,0≤X j) → X 0≤ε →
      (∀ j,X (j+1)≤A*B^j*(X j)^(1+α)) →
      Tendsto X atTop (𝓝 0) := by
  let ρ : ℝ := (2*B)^(-α⁻¹)
  let ε : ℝ := (ρ/A)^α⁻¹
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hbase : 1<2*B := by linarith
  have hρ0 : 0<ρ := Real.rpow_pos_of_pos (by linarith) _
  have hρ1 : ρ<1 := Real.rpow_lt_one_of_one_lt_of_neg hbase
    (neg_lt_zero.mpr (inv_pos.mpr hα))
  have hε : 0<ε := Real.rpow_pos_of_pos (div_pos hρ0 hA) _
  have hρpow : ρ^α=(2*B)⁻¹ := by
    dsimp only [ρ]
    rw [←Real.rpow_mul (by linarith : 0≤2*B)]
    have he : -α⁻¹*α=(-1 : ℝ) := by field_simp [hα.ne']
    rw [he,Real.rpow_neg_one]
  have hερ : A*ε^α=ρ := by
    dsimp only [ε]
    rw [←Real.rpow_mul (div_nonneg hρ0.le hA.le),inv_mul_cancel₀ hα.ne',Real.rpow_one]
    field_simp [hA.ne']
  have hBρeq : B*ρ^α=1/2 := by
    rw [hρpow]
    field_simp [hB0.ne'] <;>ring
  have hBρ : 0≤B*ρ^α ∧ B*ρ^α≤1 := by
    rw [hBρeq]
    constructor <;>norm_num
  refine ⟨ε,hε,?_⟩
  intro X hX hX0 hstep
  have hbound (j : ℕ) : X j≤ε*ρ^j := by
    induction j with
    | zero => simpa using hX0
    | succ j ih =>
      have hrpow := Real.rpow_le_rpow (hX j) ih (by linarith : 0≤1+α)
      have hfac : A*B^j*(ε*ρ^j)^(1+α)=ε*(A*ε^α)*ρ^j*(B*ρ^α)^j := by
        rw [Real.mul_rpow hε.le (pow_nonneg hρ0.le j),
          Real.rpow_add hε,Real.rpow_one,
          Real.rpow_add (pow_pos hρ0 j),Real.rpow_one,
          ←Real.rpow_pow_comm hρ0.le α j,mul_pow]
        ring
      have hpow1 : (B*ρ^α)^j≤1 := pow_le_one₀ hBρ.1 hBρ.2
      calc
        X (j+1) ≤ A*B^j*(X j)^(1+α) := hstep j
        _ ≤ A*B^j*(ε*ρ^j)^(1+α) :=
          mul_le_mul_of_nonneg_left hrpow (mul_nonneg hA.le (pow_nonneg (by linarith) j))
        _ = ε*(A*ε^α)*ρ^j*(B*ρ^α)^j := hfac
        _ ≤ ε*(A*ε^α)*ρ^j := by
          exact (mul_le_mul_of_nonneg_left hpow1 (by positivity)).trans_eq (mul_one _)
        _ = ε*ρ^(j+1) := by rw [hερ,pow_succ];ring
  have hlim : Tendsto (fun j : ℕ => ε*ρ^j) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1)
  exact squeeze_zero hX hbound hlim

/-- Scaling the dyadic truncation height makes an arbitrary finite initial
Lp tail small. The recurrence has exactly the product form supplied by the
actual weighted PDE estimate, rather than a separately assumed L-infinity bound. -/
theorem regularity_dyadic_tail_decay {A b α N : ℝ} (Y : ℝ → ℕ → ℝ)
    (hA : 0≤A) (hb : 0≤b) (hα : 0<α) (hN : 0≤N)
    (hY : ∀ K,0<K → ∀ j,0≤Y K j)
    (hinit : ∀ K,0<K → Y K 0=N)
    (hstep : ∀ K,1≤K → ∀ j,
      Y K (j+1)≤A*b^j*Y K j*
        (((K*((1/2 : ℝ)^(j+1)))⁻¹)*Y K j)^α) :
    ∃ K : ℝ, 1≤K ∧ Tendsto (Y K) atTop (𝓝 0) := by
  let A' := A*(2 : ℝ)^α+1
  let B' := max (b*(2 : ℝ)^α) 1
  have hA' : 0<A' := by dsimp only [A'];positivity
  have hB' : 1≤B' := le_max_right _ _
  obtain ⟨ε,hε,hdecay⟩ := regularity_superlinear_decay hA' hB' hα
  let K : ℝ := 1+(N+1)/ε
  have hK1 : 1<K := by
    have hpos : 0<(N+1)/ε := div_pos (by linarith) hε
    dsimp only [K]
    linarith
  have hK : 0<K := zero_lt_one.trans hK1
  let Z : ℕ → ℝ := fun j => Y K j/K
  have hZ (j : ℕ) : 0≤Z j := div_nonneg (hY K hK j) hK.le
  have hZ0 : Z 0≤ε := by
    dsimp only [Z]
    rw [hinit K hK]
    apply (div_le_iff₀ hK).mpr
    dsimp only [K]
    have he : ε*((N+1)/ε)=N+1 := by field_simp [hε.ne']
    rw [mul_add,mul_one,he]
    linarith
  have hZstep (j : ℕ) : Z (j+1)≤A'*B'^j*(Z j)^(1+α) := by
    have hinv : (((1/2 : ℝ)^(j+1)))⁻¹=(2 : ℝ)^(j+1) := by
      rw [←inv_pow]
      norm_num
    have hδ : (K*((1/2 : ℝ)^(j+1)))⁻¹*Y K j=(2 : ℝ)^(j+1)*Z j := by
      rw [mul_inv_rev,hinv]
      dsimp only [Z,div_eq_mul_inv]
      ring
    have hs := div_le_div_of_nonneg_right (hstep K hK1.le j) hK.le
    rw [hδ] at hs
    have hs' : Z (j+1)≤A*b^j*Z j*((2 : ℝ)^(j+1)*Z j)^α := by
      simpa only [Z,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hs
    have hfac : A*b^j*Z j*((2 : ℝ)^(j+1)*Z j)^α =
        (A*(2 : ℝ)^α)*(b*(2 : ℝ)^α)^j*(Z j)^(1+α) := by
      by_cases hz : Z j=0
      · simp [hz,Real.zero_rpow hα.ne',Real.zero_rpow (by linarith : 1+α≠0)]
      · have hzp : 0<Z j := (hZ j).lt_of_ne' hz
        rw [Real.mul_rpow (by positivity : 0≤(2 : ℝ)^(j+1)) (hZ j),
          ←Real.rpow_pow_comm (by norm_num : (0 : ℝ)≤2) α (j+1),
          pow_succ,mul_pow,Real.rpow_add hzp,Real.rpow_one]
        ring
    rw [hfac] at hs'
    have hC : A*(2 : ℝ)^α≤A' := by dsimp only [A'];linarith
    have hB : b*(2 : ℝ)^α≤B' := le_max_left _ _
    have hpow : (b*(2 : ℝ)^α)^j≤B'^j :=
      pow_le_pow_left₀ (mul_nonneg hb (Real.rpow_nonneg (by norm_num) _)) hB j
    exact hs'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hC hpow (pow_nonneg (mul_nonneg hb (Real.rpow_nonneg (by norm_num) _)) j)
        hA'.le) (Real.rpow_nonneg (hZ j) _))
  have hlim := hdecay Z hZ hZ0 hZstep
  refine ⟨K,hK1.le,?_⟩
  have hm := hlim.mul_const K
  convert hm using 1
  · funext j
    dsimp only [Z]
    field_simp [hK.ne']
  · simp

end BMCompactPDE

end RegularityBody_RegularityDecay

/- Body retained from RegularityLocalBounded.lean; see the adjacent exact provenance map. -/
noncomputable section RegularityBody_RegularityLocalBounded

/-! Actual local essential boundedness from arbitrary weak Lp data, using
weighted powers of one constructed smooth cutoff and the actual PDE tail
recurrence. This is a zero-source weak-subsolution theorem; positive forcing
upper regularity and selected continuous/C1 representatives are separate. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private theorem regularity_tail_finite {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hDb : Bornology.IsBounded D)
    (hη : Continuous η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (s : ℕ) (k : ℝ) :
    eLpNorm' (fun x => η x^s*max (u x-k) 0) p (volume.restrict D)≠(∞ : ℝ≥0∞) := by
  have hz : SobolevPair p D (fun x => u x-k) g := by
    exact (hu.add (sobolevPair_const hu.1 hDb (-k))).congr
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hm := hz.2.1.pos_part
  have htop : MemLp (fun x => η x^s) ∞ (volume.restrict D) :=
    memLp_top_of_bound (hη.pow s).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hη0 x) s)]
        exact pow_le_one₀ (hη0 x) (hη1 x)))
  have hf : MemLp (fun x => η x^s*max (u x-k) 0)
      (ENNReal.ofReal p) (volume.restrict D) := hm.mul' htop
  have hp0 : 0<p := zero_lt_one.trans hu.1
  simpa only [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp0.le] using hf.2.ne

set_option maxHeartbeats 800000 in
private theorem regularity_upper_bound_cutoff
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hpn : p<(n : ℝ)) :
    ∃ L : ℝ, 0<L ∧ ∀ᵐ x ∂volume.restrict D,η x=1 → u x≤L := by
  let μ := volume.restrict D
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hα : 0<p/(n : ℝ) := div_pos hp0 hn0
  obtain ⟨M,hM⟩ := exists_nat_gt p
  have hm : p≤(M : ℝ) := hM.le
  obtain ⟨G0,hG0⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).exists_bound_of_continuous
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1)
  let G : ℝ := max G0 1
  have hG : 0≤G := zero_le_one.trans (le_max_right _ _)
  have hgrad (x : Space n) (_ : x∈D) : ‖gradient η x‖≤G := (hG0 x).trans (le_max_left _ _)
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let C : ℝ := (S : ℝ)*E^p⁻¹*G
  have hC : 0≤C := mul_nonneg (mul_nonneg S.coe_nonneg (Real.rpow_nonneg (by
    dsimp only [E];positivity) _)) hG
  let k : ℝ → ℕ → ℝ := fun K j => K*(1-(1/2 : ℝ)^j)
  let Y : ℝ → ℕ → ℝ := fun K j =>
    (eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ).toReal
  let N : ℝ := Y 1 0
  have hY0 (K : ℝ) (_ : 0<K) : Y K 0=N := by simp [Y,k,N]
  have hY (K : ℝ) (_ : 0<K) (j : ℕ) : 0≤Y K j := ENNReal.toReal_nonneg
  have hfinite (s : ℕ) (l : ℝ) :
      eLpNorm' (fun x => η x^s*max (u x-l) 0) p μ≠(∞ : ℝ≥0∞) :=
    regularity_tail_finite (hu.2.2.1 D hD) hD.2.1 hη.1.continuous hη0 hη1 s l
  have hstep (K : ℝ) (hK : 0<K) (j : ℕ) :
      Y K (j+1)≤C*((M : ℝ)+1)^j*Y K j*
        (((K*((1/2 : ℝ)^(j+1)))⁻¹)*Y K j)^(p/(n : ℝ)) := by
    have hr : 0<(M+1)^j := pow_pos (Nat.zero_lt_succ M) j
    have hδ : k K (j+1)-k K j=K*(1/2 : ℝ)^(j+1) := by
      dsimp only [k]
      rw [pow_succ]
      ring
    have hδp : 0<k K (j+1)-k K j := by rw [hδ];positivity
    have hs : M*(M+1)^j+((M+1)^j-1)=(M+1)^(j+1)-1 := by
      rw [pow_succ',Nat.add_mul,Nat.one_mul]
      omega
    have he := hu.weighted_tail_step hD hη hη0 hη1 hG hgrad hr hm hpn
      (sub_pos.mp hδp)
    rw [hs] at he
    have hfin := hfinite ((M+1)^j-1) (k K j)
    have hright :
        (S*ENNReal.ofReal (E^p⁻¹)*ENNReal.ofReal ((((M+1)^j : ℕ) : ℝ)*G)*
          eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ)*
          (ENNReal.ofReal ((k K (j+1)-k K j)⁻¹)*
            eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ)^(p/(n : ℝ))≠(∞ : ℝ≥0∞) := by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top) hfin)
        (ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))
    have ht := ENNReal.toReal_mono hright he
    have hEp0 : 0≤E^p⁻¹ := Real.rpow_nonneg (by dsimp only [E];positivity) _
    have hrG0 : 0≤(((M+1)^j : ℕ) : ℝ)*G :=
      mul_nonneg (Nat.cast_nonneg _) hG
    simp only [ENNReal.toReal_mul,ENNReal.coe_toReal,
      ENNReal.toReal_ofReal hEp0,ENNReal.toReal_ofReal hrG0,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hδp.le),←ENNReal.toReal_rpow] at ht
    rw [hδ] at ht
    change Y K (j+1)≤(S : ℝ)*E^p⁻¹*
      (((((M+1)^j : ℕ) : ℝ))*G)*Y K j*
      (((K*((1/2 : ℝ)^(j+1)))⁻¹)*Y K j)^(p/(n : ℝ)) at ht
    have hcoeff : (S : ℝ)*E^p⁻¹*(((((M+1)^j : ℕ) : ℝ))*G)=
        C*((M : ℝ)+1)^j := by
      dsimp only [C]
      simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      ring
    rw [hcoeff] at ht
    exact ht
  obtain ⟨L,hL1,hlim⟩ := regularity_dyadic_tail_decay Y hC (by positivity : 0≤(M : ℝ)+1)
    hα (hY 1 zero_lt_one 0) hY hY0 (fun K hK => hstep K (zero_lt_one.trans_le hK))
  have hL : 0<L := zero_lt_one.trans_le hL1
  let F : Space n → ℝ := fun x => if η x=1 then max (u x-L) 0 else 0
  have hm : AEStronglyMeasurable (fun x => max (u x-L) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (hu.2.2.1 D hD).2.1.1
  have hF : AEStronglyMeasurable F μ :=
    hm.indicator (isClosed_eq hη.1.continuous continuous_const).measurableSet
  have hmono (j : ℕ) : eLpNorm' F p μ≤
      eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k L j) 0) p μ := by
    apply eLpNorm'_mono_ae hp0.le
    exact Eventually.of_forall (fun x => by
      have hkL : k L j≤L := by
        dsimp only [k]
        nlinarith [pow_nonneg (show (0 : ℝ)≤1/2 by norm_num) j]
      by_cases hx : η x=1
      · simp only [F,if_pos hx,hx,one_pow,one_mul,Real.norm_eq_abs,
          abs_of_nonneg (le_max_right (u x-L) 0),
          abs_of_nonneg (le_max_right (u x-k L j) 0)]
        exact max_le_max (sub_le_sub_left hkL _) le_rfl
      · simp only [F,if_neg hx,norm_zero]
        exact norm_nonneg _)
  have hFfin : eLpNorm' F p μ≠(∞ : ℝ≥0∞) :=
    ((hmono 0).trans_lt (lt_top_iff_ne_top.mpr (hfinite _ _))).ne
  have hsmall (j : ℕ) : (eLpNorm' F p μ).toReal≤Y L j :=
    ENNReal.toReal_mono (hfinite _ _) (hmono j)
  have hzle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hsmall)
  have hzreal : (eLpNorm' F p μ).toReal=0 := le_antisymm hzle ENNReal.toReal_nonneg
  have hz : eLpNorm' F p μ=0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with h|h
    · exact h
    · exact False.elim (hFfin h)
  have hae := (eLpNorm'_eq_zero_iff hp0 hF).mp hz
  refine ⟨L,hL,?_⟩
  filter_upwards [hae] with x hx
  intro hxη
  have he : max (u x-L) 0=0 := by simpa only [F,hxη,if_true,Pi.zero_apply] using hx
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq he)

private theorem regularity_compact_cutoff {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ (D : Set (Space n)) (η : Space n → ℝ),LocalDomain D Ω ∧ K⊆D ∧
      SmoothTest D η ∧ (∀ x,0≤η x) ∧ (∀ x,η x≤1) ∧ (∀ x∈K,η x=1) := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let D := thickening δ K
  have hD : LocalDomain D Ω := ⟨isOpen_thickening,hK.isBounded.thickening,
    (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  have hKD : K⊆D := self_subset_thickening hδ K
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hD.1 hKD
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest D η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1⟩
  exact ⟨D,η,hD,hKD,hη,fun x => Real.smoothTransition.nonneg _,
    fun x => Real.smoothTransition.le_one _,fun x hx =>
      Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)⟩

/-- An arbitrary actual weak subsolution with 1<p<n is essentially bounded
above on every compact subset. The upper bound is constructed from its finite
local Lp tail, not supplied as a regularity premise. -/
theorem WeakPSubsolutionPair.exists_ae_upper_bound_compact
    {n : ℕ} {p : ℝ} {Ω K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hpn : p<(n : ℝ))
    (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ L : ℝ,0<L ∧ ∀ᵐ x ∂volume.restrict K,u x≤L := by
  obtain ⟨D,η,hD,hKD,hη,hη0,hη1,hηK⟩ := regularity_compact_cutoff hu.2.1 hK hKΩ
  obtain ⟨L,hL,hae⟩ := regularity_upper_bound_cutoff hu hD hη hη0 hη1 hpn
  refine ⟨L,hL,?_⟩
  have ht := ae_restrict_of_ae_restrict_of_subset hKD hae
  filter_upwards [ht,ae_restrict_mem hK.measurableSet] with x hx hxK
  exact hx (hηK x hxK)

/-- Genuine local L-infinity membership for arbitrary actual weak harmonic
pairs. No continuous representative, pointwise bound or classical derivative
of u is assumed. This does not claim a selected continuous/C1 representative. -/
theorem WeakPHarmonicPair.memLp_top_compact
    {n : ℕ} {p : ℝ} {Ω K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hpn : p<(n : ℝ))
    (hK : IsCompact K) (hKΩ : K⊆Ω) :
    MemLp u ∞ (volume.restrict K) := by
  obtain ⟨U,hU,ha⟩ := hu.subsolution.exists_ae_upper_bound_compact hpn hK hKΩ
  obtain ⟨V,hV,hb⟩ := hu.supersolution.neg_subsolution.exists_ae_upper_bound_compact hpn hK hKΩ
  obtain ⟨D,η,hD,hKD,hη,-,-,-⟩ := regularity_compact_cutoff hu.2.1 hK hKΩ
  have hm := (MemLp.mono_measure (Measure.restrict_mono_set volume hKD)
    (hu.2.2.1 D hD).2.1).1
  apply memLp_top_of_bound hm (max U V)
  filter_upwards [ha,hb] with x hx hy
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have ht : V≤max U V := le_max_right _ _
    linarith
  · exact hx.trans (le_max_left _ _)

end BMCompactPDE

end RegularityBody_RegularityLocalBounded

#print axioms BMCompactPDE.regularity_superlinear_decay
#print axioms BMCompactPDE.regularity_dyadic_tail_decay
#print axioms BMCompactPDE.WeakPSubsolutionPair.exists_ae_upper_bound_compact
#print axioms BMCompactPDE.WeakPHarmonicPair.memLp_top_compact

end AnalyticBlock_RegularityBoundedBatch
