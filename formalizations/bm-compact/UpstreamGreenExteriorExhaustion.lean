import UpstreamGreenAnnularLimitRemainder
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic

/-! A concrete cofinal bounded open exhaustion of the actual exterior domain.
Every closure remains strictly outside the compact obstacle. Compact local
domains are eventually contained in a single member; no exhaustion premise is
assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1000000 in
theorem exists_cofinal_bounded_open_exterior_exhaustion
    {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ D : ℕ → Set (Space n),
      (∀ m,LocalDomain (D m) Kᶜ) ∧ Monotone D ∧ (⋃ m,D m)=Kᶜ ∧
      ∀ E : Set (Space n),LocalDomain E Kᶜ → ∃ m,closure E⊆D m := by
  let r : ℕ → ℝ := fun m=>(m:ℝ)+1
  let D : ℕ → Set (Space n) := fun m=>{x | ‖x‖<r m ∧ 1/r m< infDist x K}
  have hr (m : ℕ) : 0<r m := by dsimp only [r];positivity
  have hrmono : Monotone r := by
    intro m k hmk
    dsimp only [r]
    have hcast : (m:ℝ)≤(k:ℝ) := by exact_mod_cast hmk
    linarith only [hcast]
  have hDo (m : ℕ) : IsOpen (D m) :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_infDist_pt K))
  have hDb (m : ℕ) : Bornology.IsBounded (D m) :=
    (isBounded_ball (x:=(0 : Space n)) (r:=r m)).subset
      (fun x hx=>by simpa only [mem_ball,dist_zero_right] using hx.1)
  have hDcl (m : ℕ) : closure (D m)⊆Kᶜ := by
    have hc : closure (D m)⊆{x | 1/r m≤ infDist x K} :=
      closure_minimal (fun x hx=>hx.2.le)
        (isClosed_le continuous_const (continuous_infDist_pt K))
    intro x hx
    exact (hK.isClosed.notMem_iff_infDist_pos hKne).mpr
      ((one_div_pos.mpr (hr m)).trans_le (hc hx))
  have hDlocal (m : ℕ) : LocalDomain (D m) Kᶜ := ⟨hDo m,hDb m,hDcl m⟩
  have hDmono : Monotone D := by
    intro m k hmk x hx
    exact ⟨hx.1.trans_le (hrmono hmk),
      (one_div_le_one_div_of_le (hr m) (hrmono hmk)).trans_lt hx.2⟩
  have hrinf : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m=>1/r m) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hUnion : (⋃ m,D m)=Kᶜ := by
    apply Subset.antisymm
    · exact iUnion_subset (fun m=>(subset_closure.trans (hDcl m)))
    · intro x hx
      have hd : 0< infDist x K := (hK.isClosed.notMem_iff_infDist_pos hKne).mp hx
      obtain ⟨m,hm⟩ := ((hrinf.eventually (eventually_gt_atTop ‖x‖)).and
        (hinv.eventually (eventually_lt_nhds hd))).exists
      exact mem_iUnion.mpr ⟨m,hm⟩
  refine ⟨D,hDlocal,hDmono,hUnion,?_⟩
  intro E hE
  apply hE.2.1.isCompact_closure.elim_directed_cover D hDo
  · rw [hUnion]
    exact hE.2.2
  · exact hDmono.directed_le

end BMCompactPDE
#print axioms BMCompactPDE.exists_cofinal_bounded_open_exterior_exhaustion
