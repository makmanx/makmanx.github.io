import CapacityRigidMotion

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem rigid_neighborhood_preimage {n : ℕ} (e : Space n ≃ᵃⁱ[ℝ] Space n) (K : Set (Space n)) (δ : ℝ) :
    BMCompact.closedNeighborhood δ (e ⁻¹' K) = e ⁻¹' BMCompact.closedNeighborhood δ K := by
  ext x
  change infEDist x (e ⁻¹' K) ≤ ENNReal.ofReal δ ↔ infEDist (e x) K ≤ ENNReal.ofReal δ
  have he : e '' (e ⁻¹' K) = K := image_preimage_eq _ e.surjective
  rw [← Metric.infEDist_image e.isometry (x:=x) (t:=e ⁻¹' K), he]

/-- The actual selected continuous neighborhood potential is equivariant under every
Euclidean rigid motion. This supplies weak harmonicity after reflection without postulating
a regular representative or differentiability of the solution. -/
theorem ContinuousUnitCapacityData.rigid_neighborhood_scalar {n : ℕ} {p : ℝ} (hp : 1<p)
    (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) {δ : ℝ} (hδ : 0<δ)
    (e : Space n ≃ᵃⁱ[ℝ] Space n)
    (U : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ K))
    (V : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ (e ⁻¹' K))) :
    U.scalar ∘ e = V.scalar := by
  let K' := e ⁻¹' K
  let L := BMCompact.closedNeighborhood δ K
  let L' := BMCompact.closedNeighborhood δ K'
  have hK' : IsCompact K' := e.toHomeomorph.isCompact_preimage.mpr hK
  have hL : IsCompact L := BMCompact.isCompact_closedNeighborhood hK δ
  have hL' : IsCompact L' := BMCompact.isCompact_closedNeighborhood hK' δ
  have heL : L'=e ⁻¹' L := rigid_neighborhood_preimage e K δ
  obtain ⟨u,g,huc,hu1,hu,hg,_,hH,hb,hd,hen,φ,hφ,huφ,hgφ⟩ :=
    exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK hδ
  obtain ⟨v,h,hvc,hv1,hv,hh,_,hH',hb',hd',hen',hvφ⟩ :=
    exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK' hδ
  let Us : ContinuousUnitCapacityData p L := ⟨u,g,huc,hu1,hu,hH,hb,hd,hen⟩
  let Vs : ContinuousUnitCapacityData p L' := ⟨v,h,hvc,hv1,hv,hH',hb',hd',hen'⟩
  have hn1 : 1<n := by exact_mod_cast hp.trans hpn
  have eu : U.scalar = u := funext fun x => le_antisymm (U.le_of_subset (by omega) hL Subset.rfl Us x)
    (Us.le_of_subset (by omega) hL Subset.rfl U x)
  have ev : V.scalar = v := funext fun x => le_antisymm (V.le_of_subset (by omega) hL' Subset.rfl Vs x)
    (Vs.le_of_subset (by omega) hL' Subset.rfl V x)
  let E := e.linearIsometryEquiv.symm
  let g' := fun x => E (g (e x))
  have hpres := rigid_measurePreserving e
  have hgu : MemLp g' (ENNReal.ofReal p) volume := (hg.comp_measurePreserving hpres).of_le
    (E.continuous.comp_aestronglyMeasurable (hg.comp_measurePreserving hpres).1)
    (Eventually.of_forall fun x => (E.norm_map _).le)
  have heq : BMCompactCapacityV2.relativeCapacity p L' univ = ENNReal.ofReal (∫ x,‖g' x‖^p) := by
    change BMCompactCapacityV2.variationalCapacity p L' = _
    rw [heL,variationalCapacity_rigid]
    change BMCompactCapacityV2.relativeCapacity p L univ = _
    rw [hen]
    congr 1
    simpa only [g',LinearIsometryEquiv.norm_map] using
      (hpres.integral_comp e.isometry.isClosedEmbedding.measurableEmbedding (fun x => ‖g x‖^p)).symm
  rw [eu,ev]
  apply ((huc.comp e.continuous).ae_eq_iff_eq (μ:=volume) hvc).mp
  apply (variational_capacity_potentials_ae_unique hp hpn hL' (hu.comp_measurePreserving hpres) hgu
    hv hh heq hen' _ hvφ).1
  refine ⟨fun j=>φ j ∘ e,?_,?_,?_⟩
  · intro j
    change BMCompactCapacityV2.Admissible L' univ _
    rw [heL]
    exact admissible_comp_rigid e (hφ j)
  · apply huφ.congr'
    filter_upwards with j
    exact (eLpNorm_comp_measurePreserving ((hφ j).1.continuous.aestronglyMeasurable.sub hu.1) hpres).symm
  · apply hgφ.congr'
    filter_upwards with j
    have hmeas := (BMCompactCapacityV2.continuous_gradient_of_contDiff (hφ j).1).aestronglyMeasurable.sub hg.1
    change eLpNorm (gradient (φ j)-g) (ENNReal.ofReal p) volume = _
    rw [← eLpNorm_comp_measurePreserving hmeas hpres]
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    change ‖gradient (φ j) (e x)-g (e x)‖=‖gradient (φ j ∘ e) x-E (g (e x))‖
    rw [gradient_comp_rigid e (hφ j).1]
    change _ = ‖E (gradient (φ j) (e x))-E (g (e x))‖
    rw [←map_sub,E.norm_map]

end BMCompactPDE
#print axioms BMCompactPDE.rigid_neighborhood_preimage
#print axioms BMCompactPDE.ContinuousUnitCapacityData.rigid_neighborhood_scalar
