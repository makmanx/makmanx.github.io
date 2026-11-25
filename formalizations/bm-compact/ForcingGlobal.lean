import BMCompactPotentialChecked
import Mathlib.Topology.MetricSpace.Thickening

/-! The actual local constant-source equation extends to every genuine W0
test on a bounded open domain when the actual pair has global Sobolev energy.
No regularity, source-family existence or convergence assertion is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.smooth_integral_eq_global
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    (∫ x in Ω, fluxPairing p g (gradient φ) x)=c*∫ x in Ω, φ x := by
  let K := tsupport φ
  have hK : IsCompact K := hφ.2.1.isCompact
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hu.2.1 hφ.2.2
  let D : Set (Space n) := thickening δ K
  have hD : LocalDomain D Ω := ⟨isOpen_thickening,hK.isBounded.thickening,
    (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  have hKD : K⊆D := self_subset_thickening hδ K
  have hDΩ : D⊆Ω := subset_closure.trans hD.2.2
  have ht : SmoothTest D φ := ⟨hφ.1,hφ.2.1,hKD⟩
  have he := (hu.2.2.2 D hD φ (gradient φ) (ht.zeroBoundarySobolevPair hu.1)).2
  have hzero (x : Space n) (hx : x∉D) : φ x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h=>hx (hKD h))
  have hgzero (x : Space n) (hx : x∉D) : gradient φ x=0 :=
    BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun h=>hx (hKD h))
  have hI (S : Set (Space n)) (hDS : D⊆S) :
      (∫ x in S, fluxPairing p g (gradient φ) x)=∫ x, fluxPairing p g (gradient φ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by
      simp only [fluxPairing,hgzero x (fun h=>hx (hDS h)),inner_zero_right])
  have hJ (S : Set (Space n)) (hDS : D⊆S) : (∫ x in S, φ x)=∫ x, φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>hzero x (fun h=>hx (hDS h)))
  rw [hI D Subset.rfl,hJ D Subset.rfl] at he
  rw [hI Ω hDΩ,hJ Ω hDΩ]
  exact he

theorem WeakPSourcePair.integral_eq_global
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hΩb : Bornology.IsBounded Ω)
    (hSob : SobolevPair p Ω u g)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p Ω θ h) :
    Integrable (fluxPairing p g h) (volume.restrict Ω) ∧
      Integrable θ (volume.restrict Ω) ∧
      (∫ x in Ω, fluxPairing p g h x)=c*∫ x in Ω, θ x := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  haveI := holderConjugate_p_dual hu.1
  have hF := memLp_pFlux hu.1 hSob.2.2.1
  have hi := inner_integrable_of_dual_memLp hF hθ.1.2.2.1
  have hθi := hθ.1.2.1.integrable (ENNReal.one_le_ofReal.mpr hu.1.le)
  obtain ⟨hs,φ,hφ,hLu,hLg⟩ := hθ
  have hφs (j : ℕ) := (hφ j).sobolevPair hu.1
  have htF := tendsto_integral_inner_of_eLpNorm_sub_zero hF hs.2.2.1
    (fun j=>(hφs j).2.2.1) hLg
  have hOne : MemLp (fun _ : Space n => (1 : ℝ))
      (ENNReal.ofReal (p/(p-1))) (volume.restrict Ω) := memLp_const 1
  have htθ : Tendsto (fun j=>∫ x in Ω, φ j x) atTop (𝓝 (∫ x in Ω, θ x)) := by
    simpa only [Real.inner_apply,one_mul] using
      tendsto_integral_inner_of_eLpNorm_sub_zero hOne hs.2.1
        (fun j=>(hφs j).2.1) hLu
  have he (j : ℕ) := hu.smooth_integral_eq_global (hφ j)
  refine ⟨hi,hθi,?_⟩
  exact tendsto_nhds_unique htF
    ((htθ.const_mul c).congr' (Eventually.of_forall (fun j=>(he j).symm)))

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.smooth_integral_eq_global
#print axioms BMCompactPDE.WeakPSourcePair.integral_eq_global
