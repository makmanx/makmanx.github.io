import ExteriorCapacityConstruction

/-! Uniqueness of the actual variational capacitary minimum in its concrete
function-valued homogeneous graph. This removes the minimizing-choice ambiguity;
it is not a boundary-trace or canonical Green identification theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem boundary_capacity_minimum_unique {n : ℕ} (p q : ℝ)
    [Fact (1≤ENNReal.ofReal p)] [Fact (1≤ENNReal.ofReal q)]
    (hp : 1<p) (hpn : p<(n : ℝ)) (hq : q=(n : ℝ)*p/((n : ℝ)-p))
    {K : Set (Space n)} {u v : exteriorHomogeneousGraph p q n}
    (hu : u∈exteriorCapacityClass p q K) (hv : v∈exteriorCapacityClass p q K)
    (hmu : ∀ z∈exteriorCapacityClass p q K,‖u.1.2‖^p≤‖z.1.2‖^p)
    (hmv : ∀ z∈exteriorCapacityClass p q K,‖v.1.2‖^p≤‖z.1.2‖^p) : u=v := by
  obtain ⟨A,hA⟩ := exists_exteriorHomogeneousGradient_antilipschitz p q hp hpn hq
  apply hA.injective
  change u.1.2=v.1.2
  by_contra hne
  obtain ⟨κ,hκ,hgap⟩ := BMCompactBanach.lp_bounded_midpoint_gap
    (E:=Space n) (μ:=(volume : Measure (Space n))) hp (max ‖u.1.2‖ ‖v.1.2‖)
    ‖u.1.2-v.1.2‖ (norm_sub_pos_iff.mpr hne)
  have hg := hgap u.1.2 v.1.2 (le_max_left _ _) (le_max_right _ _) le_rfl
  have hmid := convex_exteriorCapacityClass p q K hu hv
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  have hm := hmu _ hmid
  have he : ‖u.1.2‖^p=‖v.1.2‖^p := le_antisymm (hmu v hv) (hmv u hu)
  have hgrad : ((1/2 : ℝ) • u+(1/2 : ℝ) • v).1.2=
      (1/2 : ℝ) • (u.1.2+v.1.2) := by
    change (1/2 : ℝ) • u.1.2+(1/2 : ℝ) • v.1.2=_
    rw [smul_add]
  rw [hgrad] at hm
  rw [←he] at hg
  linarith only [hκ,hg,hm]

/-- Every actual compact set has a unique minimum in the closure of all genuine
smooth capacity-admissible pairs; the minimum and uniqueness are constructed. -/
theorem existsUnique_exteriorCapacityClass_minimum {n : ℕ} (p q : ℝ)
    [Fact (1≤ENNReal.ofReal p)] [Fact (1≤ENNReal.ofReal q)]
    (hp : 1<p) (hpn : p<(n : ℝ)) (hq : q=(n : ℝ)*p/((n : ℝ)-p))
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃! w : exteriorHomogeneousGraph p q n,
      w∈exteriorCapacityClass p q K ∧
      ∀ z∈exteriorCapacityClass p q K,‖w.1.2‖^p≤‖z.1.2‖^p := by
  obtain ⟨w,hw,hm⟩ := exists_exteriorCapacityClass_minimum p q hp hpn hq hK
  refine ⟨w,⟨hw,hm⟩,?_⟩
  intro v hv
  exact boundary_capacity_minimum_unique p q hp hpn hq hv.1 hw hv.2 hm

end BMCompactPDE
#print axioms BMCompactPDE.existsUnique_exteriorCapacityClass_minimum
