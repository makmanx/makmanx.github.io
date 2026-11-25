import SmoothWeakBridge
import WeakSobolevAE
import WeakHarmonicScaling

/-! Real affine and local-representative invariance of the actual weak
p-Laplace equation. Adding a constant leaves the weak gradient unchanged.
This does not assert linearity in the gradient or a comparison theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem LocallySobolevPair.add_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : LocallySobolevPair p Ω u g) (hp : 1 < p) (c : ℝ) :
    LocallySobolevPair p Ω (fun x => u x + c) g := by
  intro D hD
  have hs := (hu D hD).add (sobolevPair_const hp hD.2.1 c)
  exact hs.congr
    (Eventually.of_forall (fun x => by simp only [Pi.add_apply]))
    (Eventually.of_forall (fun x => by simp))

theorem WeakPHarmonicPair.add_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (c : ℝ) :
    WeakPHarmonicPair p Ω (fun x => u x + c) g :=
  ⟨hu.1, hu.2.1, hu.2.2.1.add_const hu.1 c, hu.2.2.2⟩

theorem IsWeakPHarmonic.add_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (c : ℝ) :
    IsWeakPHarmonic p Ω (fun x => u x + c) := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, hg.add_const c⟩

theorem WeakPHarmonicPair.sub_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (c : ℝ) :
    WeakPHarmonicPair p Ω (fun x => u x - c) g := by
  simpa only [sub_eq_add_neg] using hu.add_const (-c)

theorem IsWeakPHarmonic.sub_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (c : ℝ) :
    IsWeakPHarmonic p Ω (fun x => u x - c) := by
  simpa only [sub_eq_add_neg] using hu.add_const (-c)

theorem LocallySobolevPair.congr_fun {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g : Space n → Space n}
    (hu : LocallySobolevPair p Ω u g) (huv : EqOn u v Ω) :
    LocallySobolevPair p Ω v g := by
  intro D hD
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have huvAE : u =ᵐ[volume.restrict D] v := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    exact huv (hDΩ hx)
  exact (hu D hD).congr huvAE (EventuallyEq.rfl)

theorem WeakPHarmonicPair.congr_fun {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (huv : EqOn u v Ω) :
    WeakPHarmonicPair p Ω v g :=
  ⟨hu.1, hu.2.1, hu.2.2.1.congr_fun huv, hu.2.2.2⟩

theorem IsWeakPHarmonic.congr_on {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (huv : EqOn u v Ω) :
    IsWeakPHarmonic p Ω v := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, hg.congr_fun huv⟩

end BMCompactPDE
#print axioms BMCompactPDE.LocallySobolevPair.add_const
#print axioms BMCompactPDE.WeakPHarmonicPair.add_const
#print axioms BMCompactPDE.IsWeakPHarmonic.add_const
#print axioms BMCompactPDE.WeakPHarmonicPair.sub_const
#print axioms BMCompactPDE.IsWeakPHarmonic.sub_const
#print axioms BMCompactPDE.LocallySobolevPair.congr_fun
#print axioms BMCompactPDE.WeakPHarmonicPair.congr_fun
#print axioms BMCompactPDE.IsWeakPHarmonic.congr_on
