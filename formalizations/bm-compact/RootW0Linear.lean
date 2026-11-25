import BMCompactChecked
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Actual linear W0 graph operations, with constructed smooth approximants.
These are not assumptions that the distributional graph is a vector space. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem gradient_add_smooth_actual {n : ℕ} {f h : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) :
    gradient (f+h)=gradient f+gradient h := by
  funext x
  unfold gradient
  rw [fderiv_add (hf.differentiable (by simp) x) (hh.differentiable (by simp) x)]
  exact map_add _ _ _

theorem gradient_smul_smooth_actual {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) : gradient (c • f)=c • gradient f := by
  funext x
  unfold gradient
  rw [fderiv_const_smul (hf.differentiable (by simp) x)]
  exact map_smul _ _ _

theorem ZeroBoundarySobolevPair.add_actual {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hv : ZeroBoundarySobolevPair p D v h) :
    ZeroBoundarySobolevPair p D (u+v) (g+h) := by
  obtain ⟨su,φ,hφ,hφu,hφg⟩ := hu
  obtain ⟨sv,ψ,hψ,hψv,hψh⟩ := hv
  let q := ENNReal.ofReal p
  let μ := volume.restrict D
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr su.1.le
  have ht (j : ℕ) : SmoothTest D (φ j+ψ j) :=
    ⟨(hφ j).1.add (hψ j).1,(hφ j).2.1.add (hψ j).2.1,
      (tsupport_add _ _).trans (union_subset (hφ j).2.2 (hψ j).2.2)⟩
  refine ⟨su.add sv,fun j=>φ j+ψ j,ht,?_,?_⟩
  · have hl := hφu.add hψv
    rw [add_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _=>bot_le)
    intro j
    change eLpNorm (φ j+ψ j-(u+v)) q μ ≤ eLpNorm (φ j-u) q μ+eLpNorm (ψ j-v) q μ
    have he : φ j+ψ j-(u+v)=(φ j-u)+(ψ j-v) := by abel
    rw [he]
    exact eLpNorm_add_le (((hφ j).sobolevPair su.1).2.1.sub su.2.1).1
      (((hψ j).sobolevPair su.1).2.1.sub sv.2.1).1 hq
  · have hl := hφg.add hψh
    rw [add_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _=>bot_le)
    intro j
    change eLpNorm (fun x => gradient (φ j+ψ j) x-(g+h) x) q μ ≤
      eLpNorm (fun x=>gradient (φ j) x-g x) q μ+eLpNorm (fun x=>gradient (ψ j) x-h x) q μ
    rw [gradient_add_smooth_actual (hφ j).1 (hψ j).1]
    have he : (fun x => (gradient (φ j)+gradient (ψ j)) x-(g+h) x) =
        (gradient (φ j)-g)+(gradient (ψ j)-h) := by
      funext x
      simp only [Pi.add_apply,Pi.sub_apply]
      abel
    rw [he]
    exact eLpNorm_add_le (((hφ j).sobolevPair su.1).2.2.1.sub su.2.2.1).1
      (((hψ j).sobolevPair su.1).2.2.1.sub sv.2.2.1).1 hq

set_option maxHeartbeats 1000000 in
theorem ZeroBoundarySobolevPair.smul_actual {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (c : ℝ) :
    ZeroBoundarySobolevPair p D (c • u) (c • g) := by
  obtain ⟨su,φ,hφ,hφu,hφg⟩ := hu
  have ht (j : ℕ) : SmoothTest D (c • φ j) :=
    ⟨(hφ j).1.const_smul c,(hφ j).2.1.isCompact.of_isClosed_subset (isClosed_tsupport (c • φ j))
      (tsupport_smul_subset_right (fun _ : Space n => c) (φ j)),
      (tsupport_smul_subset_right (fun _ : Space n => c) (φ j)).trans (hφ j).2.2⟩
  refine ⟨su.smul c,fun j=>c • φ j,ht,?_,?_⟩
  · have he (j : ℕ) : c • φ j-c • u=c • (φ j-u) := by simp only [smul_sub]
    simp_rw [he,eLpNorm_const_smul]
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hφu (Or.inr (by simp : ‖c‖ₑ≠(∞ : ℝ≥0∞)))
  · have hgrad (j : ℕ) : gradient (c • φ j)=c • gradient (φ j) :=
      gradient_smul_smooth_actual (hφ j).1 c
    simp_rw [hgrad]
    have he (j : ℕ) : (fun x => (c • gradient (φ j)) x-(c • g) x)=
        c • (fun x => gradient (φ j) x-g x) := by
      funext x
      simp only [Pi.smul_apply,smul_sub]
    simp_rw [he,eLpNorm_const_smul]
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hφg (Or.inr (by simp : ‖c‖ₑ≠(∞ : ℝ≥0∞)))

theorem ZeroBoundarySobolevPair.sub_actual {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g) (hv : ZeroBoundarySobolevPair p D v h) :
    ZeroBoundarySobolevPair p D (u-v) (g-h) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hu.add_actual (hv.smul_actual (-1))

/-- Restrict the actual distributional Sobolev graph; both representatives are
unchanged. Smooth-test supports remove the difference of integration domains. -/
theorem SobolevPair.mono_actual {n : ℕ} {p : ℝ} {D Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hDΩ : D ⊆ Ω) : SobolevPair p D u g := by
  refine ⟨hu.1,hu.2.1.mono_measure (Measure.restrict_mono hDΩ le_rfl),
    hu.2.2.1.mono_measure (Measure.restrict_mono hDΩ le_rfl),?_⟩
  intro φ hφ i
  have ht : SmoothTest Ω φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hDΩ⟩
  obtain ⟨hi,hj,he⟩ := hu.2.2.2 φ ht i
  have hφ0 (x : Space n) (hx : x∉D) : φ x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h=>hx (hφ.2.2 h))
  have hgrad0 (x : Space n) (hx : x∉D) : gradient φ x=0 :=
    BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun h=>hx (hφ.2.2 h))
  have hIL (S : Set (Space n)) (hDS : D ⊆ S) :
      (∫ x in S, u x*gradient φ x i)=∫ x, u x*gradient φ x i :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by
      rw [hgrad0 x (fun h=>hx (hDS h))];simp)
  have hIR (S : Set (Space n)) (hDS : D ⊆ S) :
      (∫ x in S, g x i*φ x)=∫ x, g x i*φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by
      rw [hφ0 x (fun h=>hx (hDS h)),mul_zero])
  rw [hIL Ω hDΩ,hIR Ω hDΩ] at he
  exact ⟨IntegrableOn.mono_set hi hDΩ,IntegrableOn.mono_set hj hDΩ,
    by rw [hIL D Subset.rfl,hIR D Subset.rfl];exact he⟩

theorem SobolevPair.locally_actual {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n} (hu : SobolevPair p Ω u g) :
    LocallySobolevPair p Ω u g := by
  intro D hD
  exact hu.mono_actual (subset_closure.trans hD.2.2)

theorem weakPHarmonicPair_of_sobolev_smooth_equation {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g)
    (he : ∀ φ : Space n → ℝ, SmoothTest Ω φ →
      (∫ x in Ω, fluxPairing p g (gradient φ) x)=0) : WeakPHarmonicPair p Ω u g := by
  apply weakPHarmonicPair_of_smooth_test_equation hu.1 hΩ hu.locally_actual
  intro D hD φ hφ
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have ht : SmoothTest Ω φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hDΩ⟩
  have hzero (x : Space n) (hx : x∉D) : fluxPairing p g (gradient φ) x=0 := by
    have hg : gradient φ x=0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      (fun h=>hx (hφ.2.2 h))
    simp only [fluxPairing,hg,inner_zero_right]
  have hI (S : Set (Space n)) (hDS : D ⊆ S) :
      (∫ x in S, fluxPairing p g (gradient φ) x)=∫ x, fluxPairing p g (gradient φ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>hzero x (fun h=>hx (hDS h)))
  rw [hI D Subset.rfl,←hI Ω hDΩ]
  exact he φ ht

end BMCompactPDE
#print axioms BMCompactPDE.gradient_add_smooth_actual
#print axioms BMCompactPDE.gradient_smul_smooth_actual
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.add_actual
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.smul_actual
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.sub_actual

#print axioms BMCompactPDE.SobolevPair.mono_actual
#print axioms BMCompactPDE.SobolevPair.locally_actual
#print axioms BMCompactPDE.weakPHarmonicPair_of_sobolev_smooth_equation
