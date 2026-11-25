import RootSobolevMultiplier
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Genuine global extension for compactly supported Sobolev pairs and
actual smooth localization. No boundary trace, density or C1 premise for the
original Sobolev representative is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem tsupport_gradient_subset_actual {n : ℕ} (f : Space n → ℝ) :
    tsupport (gradient f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  change gradient f x ≠ 0 at hx
  exact hx (BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hn)

theorem memLp_global_of_restrict_zero_outside {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {q : ℝ≥0∞} {Ω : Set (Space n)} (hΩ : MeasurableSet Ω)
    {f : Space n → F} (hf : MemLp f q (volume.restrict Ω))
    (hz : ∀ x, x∉Ω → f x=0) : MemLp f q volume := by
  have he : Ω.indicator f = f := by
    funext x
    by_cases hx : x∈Ω
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx,hz x hx]
  simpa only [he] using (memLp_indicator_iff_restrict hΩ).mpr hf

/-- Compact support inside an open domain permits genuine extension of the
actual distributional graph to the whole space, with the same representatives. -/
theorem SobolevPair.global_of_compact_support {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (huK : tsupport u ⊆ K) (hgK : tsupport g ⊆ K) (hKΩ : K ⊆ Ω) :
    SobolevPair p univ u g := by
  have hu0 (x : Space n) (hx : x∉K) : u x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx (huK hy))
  have hg0 (x : Space n) (hx : x∉K) : g x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx (hgK hy))
  have huΩ0 (x : Space n) (hx : x∉Ω) : u x=0 := hu0 x (fun hy => hx (hKΩ hy))
  have hgΩ0 (x : Space n) (hx : x∉Ω) : g x=0 := hg0 x (fun hy => hx (hKΩ hy))
  have hum := memLp_global_of_restrict_zero_outside hΩ.measurableSet hu.2.1 huΩ0
  have hgm := memLp_global_of_restrict_zero_outside hΩ.measurableSet hu.2.2.1 hgΩ0
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hχs : tsupport χ ⊆ Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) f).trans hf.2.2.1
  have hχ1 (x : Space n) (hx : x∈K) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hχg (x : Space n) (hx : x∈K) : gradient χ x=0 := by
    have hm : IsLocalMax χ x := Eventually.of_forall (fun y => by
      rw [hχ1 x hx]
      exact Real.smoothTransition.le_one (f y))
    unfold gradient
    rw [hm.fderiv_eq_zero]
    exact map_zero _
  refine ⟨hu.1,by simpa using hum,by simpa using hgm,?_⟩
  intro φ hφ i
  have ht : SmoothTest Ω (fun x => χ x*φ x) :=
    ⟨hχ.mul hφ.1,hφ.2.1.mul_left,tsupport_mul_subset_left.trans hχs⟩
  obtain ⟨hi,hj,he⟩ := hu.2.2.2 _ ht i
  have heL : (fun x => u x*gradient (fun y => χ y*φ y) x i) =
      (fun x => u x*gradient φ x i) := by
    funext x
    by_cases hx : x∈K
    · rw [gradient_fun_mul_actual (hχ.differentiable (by simp) x)
        (hφ.1.differentiable (by simp) x),hχ1 x hx,hχg x hx]
      simp
    · simp only [hu0 x hx,zero_mul]
  have heR : (fun x => g x i*(χ x*φ x)) = (fun x => g x i*φ x) := by
    funext x
    by_cases hx : x∈K
    · rw [hχ1 x hx,one_mul]
    · simp only [hg0 x hx,PiLp.zero_apply,zero_mul]
  rw [heL] at hi he
  rw [heR] at hj he
  have hiG : Integrable (fun x => u x*gradient φ x i) volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero hi (fun x hx => by rw [huΩ0 x hx,zero_mul])
  have hjG : Integrable (fun x => g x i*φ x) volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero hj (fun x hx => by rw [hgΩ0 x hx]; simp)
  have hIL : (∫ x in Ω, u x*gradient φ x i) = ∫ x, u x*gradient φ x i :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [huΩ0 x hx,zero_mul])
  have hIR : (∫ x in Ω, g x i*φ x) = ∫ x, g x i*φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hgΩ0 x hx]; simp)
  rw [hIL,hIR] at he
  simpa only [Measure.restrict_univ] using And.intro hiG (And.intro hjG he)

/-- Smooth compact localization constructs a whole-space actual Sobolev pair
from a pair known only on its open domain. -/
theorem SobolevPair.mul_smooth_compactSupport_global {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) {χ : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    SobolevPair p univ (fun x => χ x*u x)
      (fun x => χ x • g x+u x • gradient χ x) := by
  have hlocal := hu.mul_smooth_compactSupport hχ hc
  apply hlocal.global_of_compact_support hΩ hc.isCompact tsupport_mul_subset_left _ hs
  exact (tsupport_add _ _).trans (union_subset (tsupport_smul_subset_left χ g)
    ((tsupport_smul_subset_right u (gradient χ)).trans (tsupport_gradient_subset_actual χ)))

end BMCompactPDE
#print axioms BMCompactPDE.tsupport_gradient_subset_actual
#print axioms BMCompactPDE.memLp_global_of_restrict_zero_outside
#print axioms BMCompactPDE.SobolevPair.global_of_compact_support
#print axioms BMCompactPDE.SobolevPair.mul_smooth_compactSupport_global
