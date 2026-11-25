import NonlinearAnalyticBatch
import ExteriorCapacityBridge

/-! Strong graph closure of the ACTUAL weak p-harmonic PDE. Strong scalar and
gradient Lp convergence are explicit inputs; the weak gradient, energy
minimality and full local W0 equation of the limit are derived. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1000000 in
theorem weakPHarmonicPair_of_actual_strong_Lp_limits
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hSob : ∀ j,SobolevPair p Ω (u j) (g j))
    (hPDE : ∀ j,WeakPHarmonicPair p Ω (u j) (g j))
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict Ω))
    (hh : MemLp h (ENNReal.ofReal p) (volume.restrict Ω))
    (hlimu : Tendsto (fun j=>eLpNorm (u j-v) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (g j-h) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0)) :
    SobolevPair p Ω v h ∧ WeakPHarmonicPair p Ω v h := by
  have hs : SobolevPair p Ω v h :=
    sobolevPair_of_eLpNorm_limits hp hSob hv hh hlimu hlimg
  have he0 := exterior_integral_energy_tendsto_of_Lp hp
    (fun j=>(hSob j).2.2.1) hh hlimg
  have hmin (θ : Space n → ℝ) (k : Space n → Space n)
      (hθ : ZeroBoundarySobolevPair p Ω θ k) :
      (∫ x in Ω,‖h x‖^p)≤(∫ x in Ω,‖h x+k x‖^p)-p*0*(∫ x in Ω,θ x) := by
    have hk := hθ.1.2.2.1
    have hlim : Tendsto (fun j=>eLpNorm (fun x=>(g j x+k x)-(h x+k x))
        (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
      have heq (j : ℕ) : (fun x=>(g j x+k x)-(h x+k x))=g j-h := by
        funext x
        exact add_sub_add_right_eq_sub (g j x) (h x) (k x)
      simpa only [heq] using hlimg
    have hek := exterior_integral_energy_tendsto_of_Lp hp
      (fun j=>(hSob j).2.2.1.add hk) (hh.add hk) hlim
    have hle : (∫ x in Ω,‖h x‖^p)≤∫ x in Ω,‖h x+k x‖^p :=
      le_of_tendsto_of_tendsto' he0 hek (fun j=>by
        simpa only [mul_zero,zero_mul,add_zero,Pi.add_apply] using
          (hPDE j).source_zero.energy_tangent_global hΩb (hSob j) hθ)
    simpa only [mul_zero,zero_mul,sub_zero] using hle
  have hsource : WeakPSourcePair p 0 Ω v h :=
    weakPSourcePair_of_sobolev_smooth_source_equation hΩ hs (by
      intro φ hφ
      have he := source_flux_identity_of_actual_energy_minimum hp hh hmin
        (hφ.zeroBoundarySobolevPair hp)
      simpa only [fluxPairing] using he.2)
  exact ⟨hs,hsource.harmonic_of_source_zero⟩

end BMCompactPDE
#print axioms BMCompactPDE.weakPHarmonicPair_of_actual_strong_Lp_limits
