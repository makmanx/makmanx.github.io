import CriticalOuterGreenLimit
import CriticalBallComparison

noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology Pointwise
namespace BMCompactPDE

/-- The manuscript's outer Green field is the all-positive-radius limit
of actual canonically normalized weak Green potentials on the thickened set. -/
def IsCriticalOuterGreen {n : ℕ} (K : Set (Space n)) (v : Space n → ℝ≥0∞) : Prop :=
  ∃ G : Ioi (0:ℝ) → Space n → ℝ,
    (∀ r, IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val K) (G r)) ∧
    ∀ x, Tendsto (fun r => ENNReal.ofReal (G r x)) atBot (𝓝 (v x))

theorem IsCriticalOuterGreen.unique {n : ℕ} {K : Set (Space n)} {v w : Space n → ℝ≥0∞}
    (hv : IsCriticalOuterGreen K v) (hw : IsCriticalOuterGreen K w) : v = w := by
  let _ : Nonempty (Ioi (0:ℝ)) := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  obtain ⟨G,hG,hl⟩ := hv
  obtain ⟨H,hH,hm⟩ := hw
  have eq : G = H := funext (fun r => (hG r).unique (hH r))
  subst H
  exact funext (fun x => tendsto_nhds_unique (hl x) (hm x))

theorem existsUnique_critical_outer_green {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) : ∃! v, IsCriticalOuterGreen K v := by
  obtain ⟨G,L,hG,_,hl,_⟩ := exists_critical_outer_green_limit hn hK hne
  have h : IsCriticalOuterGreen K L := ⟨G,hG,hl⟩
  exact ⟨L,h,fun _ hw => hw.unique h⟩

/-- Critical C(c) for closed balls with arbitrary centers and nonnegative
radii. In particular, the limits at a singleton are treated in [0,∞]. -/
theorem theoremC_critical_outer_closedBalls {n : ℕ} (hn : 2 ≤ n) (a b : Space n)
    {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ u v w : Space n → ℝ≥0∞, IsCriticalOuterGreen (closedBall a r) u ∧
      IsCriticalOuterGreen (closedBall b s) v ∧
      IsCriticalOuterGreen (t • closedBall a r + (1-t) • closedBall b s) w ∧
      ∀ x y, w (t • x + (1-t) • y) ≤ max (u x) (v y) := by
  have hn' : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hσ := canonicalSphereArea_pos (show 0 < n by omega)
  obtain ⟨U,V,W,u,v,w,hG,hl,hcomp⟩ := theoremC_critical_outer_of_neighborhood_comparison
    hn ht ht1 (isCompact_closedBall a r) ⟨a,mem_closedBall_self hr⟩
    (isCompact_closedBall b s) ⟨b,mem_closedBall_self hs⟩ (by
      intro δ A B C hA hB hC x y
      simp only [BMCompact.closedNeighborhood,cthickening_closedBall δ.property.le hr,
        cthickening_closedBall δ.property.le hs] at hA hB hC
      exact theoremC_critical_closedBalls hn' hσ (add_pos_of_pos_of_nonneg δ.property hr)
        (add_pos_of_pos_of_nonneg δ.property hs) ht ht1 a b hA hB hC x y)
  exact ⟨u,v,w,⟨U,fun δ => (hG δ).1,fun x => (hl x).1⟩,
    ⟨V,fun δ => (hG δ).2.1,fun x => (hl x).2.1⟩,
    ⟨W,fun δ => (hG δ).2.2,fun x => (hl x).2.2⟩,hcomp⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsCriticalOuterGreen.unique
#print axioms BMCompactPDE.existsUnique_critical_outer_green
#print axioms BMCompactPDE.theoremC_critical_outer_closedBalls
