import WeakPDE

/-! The concrete weak/Sobolev definitions depend only on almost-everywhere
representatives on their domain, as genuine Sobolev objects must. -/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem HasWeakGradientOn.congr {n : ℕ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : HasWeakGradientOn D u g)
    (huv : u =ᵐ[volume.restrict D] v) (hgh : g =ᵐ[volume.restrict D] h) :
    HasWeakGradientOn D v h := by
  intro φ hφ i
  obtain ⟨hui, hgi, hEq⟩ := hu φ hφ i
  have ha : (fun x => u x * (gradient φ x) i) =ᵐ[volume.restrict D]
      (fun x => v x * (gradient φ x) i) :=
    huv.mono (fun x hx => by dsimp only; rw [hx])
  have hb : (fun x => (g x) i * φ x) =ᵐ[volume.restrict D]
      (fun x => (h x) i * φ x) :=
    hgh.mono (fun x hx => by dsimp only; rw [hx])
  refine ⟨hui.congr ha, hgi.congr hb, ?_⟩
  rw [← integral_congr_ae ha, ← integral_congr_ae hb]
  exact hEq

theorem SobolevPair.congr {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : SobolevPair p D u g)
    (huv : u =ᵐ[volume.restrict D] v) (hgh : g =ᵐ[volume.restrict D] h) :
    SobolevPair p D v h :=
  ⟨hu.1, MemLp.ae_eq huv hu.2.1, MemLp.ae_eq hgh hu.2.2.1,
    hu.2.2.2.congr huv hgh⟩

theorem ZeroBoundarySobolevPair.congr {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p D u g)
    (huv : u =ᵐ[volume.restrict D] v) (hgh : g =ᵐ[volume.restrict D] h) :
    ZeroBoundarySobolevPair p D v h := by
  obtain ⟨hSob, φ, hφ, hlimu, hlimg⟩ := hu
  refine ⟨hSob.congr huv hgh, φ, hφ, ?_, ?_⟩
  · have heq : (fun j => eLpNorm (φ j - v) (ENNReal.ofReal p) (volume.restrict D)) =
        (fun j => eLpNorm (φ j - u) (ENNReal.ofReal p) (volume.restrict D)) := by
      funext j
      exact eLpNorm_congr_ae (huv.symm.mono (fun x hx => by simp only [Pi.sub_apply, hx]))
    rw [heq]
    exact hlimu
  · have heq : (fun j => eLpNorm (fun x => gradient (φ j) x - h x)
        (ENNReal.ofReal p) (volume.restrict D)) =
        (fun j => eLpNorm (fun x => gradient (φ j) x - g x)
          (ENNReal.ofReal p) (volume.restrict D)) := by
      funext j
      exact eLpNorm_congr_ae (hgh.symm.mono (fun x hx => by dsimp only; rw [hx]))
    rw [heq]
    exact hlimg

end BMCompactPDE

#print axioms BMCompactPDE.HasWeakGradientOn.congr
#print axioms BMCompactPDE.SobolevPair.congr
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.congr
