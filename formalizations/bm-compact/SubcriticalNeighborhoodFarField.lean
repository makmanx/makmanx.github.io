import NeighborhoodReflectionOrder
import SubcriticalReflectionLimit
import SubcriticalMassIdentification
import UnitPotentialSigns

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology BMCompactCapacityV2
open scoped Topology ENNReal Pointwise
namespace BMCompactPDE

/-- In every subcritical exponent, the normalized exterior potential on
a positive closed neighborhood has a unique far-field coefficient. Its
actual nonlinear flux identifies the coefficient with original capacity. -/
theorem ContinuousUnitCapacityData.subcritical_neighborhood_far_field {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty)
    {δ : ℝ} (hδ : 0<δ) (U : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ K)) :
    ∃ a : ℝ, 0<a ∧ Tendsto (fun x=>‖x‖^(((n:ℝ)-p)/(p-1))*U.scalar x) (cocompact _) (𝓝 a) ∧
      a^(p-1)*(((n:ℝ)-p)/(p-1))^(p-1)*canonicalSphereArea n =
        (variationalCapacity p (BMCompact.closedNeighborhood δ K)).toReal := by
  let L := BMCompact.closedNeighborhood δ K
  have hL : IsCompact L := BMCompact.isCompact_closedNeighborhood hK δ
  obtain ⟨R,hR,hLR⟩ := hL.isBounded.subset_ball_lt 0 (0:Space n)
  have hn1 : 1<n := by exact_mod_cast hp.trans hpn
  have hw := U.harmonic.mono (compl_subset_compl.mpr (hLR.trans ball_subset_closedBall))
    isClosed_closedBall.isOpen_compl
  obtain ⟨a,ha,hl⟩ := hw.subcritical_positive_normalized_limit_of_separated_order
    (by omega) hpn hR (show 0<2*R by linarith) U.continuous_scalar.continuousOn U.decay
    (fun x y _ hgap=>U.reflection_far_order hp hpn hK hδ hR hLR x y hgap)
    (fun x _=>U.pos_of_nonempty (by omega) hL (hk.mono (BMCompact.subset_closedNeighborhood K δ)) x)
  exact ⟨a,ha,hl,U.subcritical_neighborhood_mass_of_far_field (by omega) hp hpn hK hδ ha hl⟩

end BMCompactPDE
#print axioms BMCompactPDE.ContinuousUnitCapacityData.subcritical_neighborhood_far_field
