import WeakPDE
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Transfer actual almost-everywhere scalar order to pointwise order between
continuous representatives on an open Euclidean domain. This is the full-
support step used AFTER constructing a weak Green limit and selecting C0;
it does not assert that the original raw pointwise limit equals that selection
at every point, or that the approximants converge uniformly. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace BMCompactPDE

theorem leOn_of_ae_le_continuousOn_actual
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f g : Space n → ℝ} (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (hfg : ∀ᵐ x ∂volume.restrict Ω,f x≤g x) : ∀ x∈Ω,f x≤g x := by
  have hz : (fun x=>max (f x-g x) 0)=ᵐ[volume.restrict Ω] (fun _=>0) := by
    filter_upwards [hfg] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have hc : ContinuousOn (fun x=>max (f x-g x) 0) Ω :=
    ((show Continuous (fun t : ℝ=>max t 0) by fun_prop).comp_continuousOn (hf.sub hg))
  have he := Measure.eqOn_open_of_ae_eq hz hΩ hc continuousOn_const
  intro x hx
  exact sub_nonpos.mp ((le_max_left (f x-g x) 0).trans_eq (he hx))

end BMCompactPDE
#print axioms BMCompactPDE.leOn_of_ae_le_continuousOn_actual
