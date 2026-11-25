import CriticalGreenSelectedBoundary
import NextCriticalAnnularLower
import NextCriticalAnnularFamily
import NextComparisonAnnularWeakLimit
import UpstreamGreenTranslation
import UpstreamBoundaryGreenUnique

/-! The logarithmic Green function for compact obstacles admitting interior
tangent balls. Its weak equation is obtained from local strong Sobolev limits.
A single finite annulus controls its trace. Logarithmic profiles for a
contained and a containing ball bound the remainder at infinity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology
open scoped Topology
namespace BMCompactPDE

theorem exists_critical_exterior_green_with_concentric_bounds
    {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hinner : closedBall (0 : Space n) r ⊆ K)
    (hballs : ∀ a ∈ K, ∃ z : Space n, ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ K ∧ dist a z = s) :
    ∃ w : Space n → ℝ, ∃ g : Space n → Space n,
      IsExteriorGreen n (canonicalSphereArea n) n K w ∧ WeakPHarmonicPair (n : ℝ) Kᶜ w g ∧
      ∃ a : ℝ, r < a ∧ K ⊆ closedBall (0 : Space n) a ∧ ∀ x,
        ballGreen n (canonicalSphereArea n) n a x ≤ w x ∧
        w x ≤ ballGreen n (canonicalSphereArea n) n r x := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hKne : K.Nonempty := ⟨0,hinner (mem_closedBall_self hr.le)⟩
  obtain ⟨R,G,Γ,hRK,hRm,hRlim,hGc,hGK,hout,_,hSob,hPDE,hB,horder,_⟩ :=
    exists_canonical_critical_annular_green_family_of_interior_balls hn hK hr hinner hballs
  obtain ⟨v,w,g,hpoint,_,_,hwc,hvw,hwK,hwB,hwPDE,_⟩ :=
    exists_selected_weak_limit_of_bounded_annular_family hn (by exact_mod_cast hn : 2 ≤ (n : ℝ))
      hK hKne hRm.monotone hRlim hGc hGK hSob hPDE
      (continuous_ballGreen n (canonicalSphereArea n) (n : ℝ) hr) hB horder
  have hc := continuous_selected_annular_limit_at_obstacle hK.isClosed isOpen_ball (hRK 0).2
    (hGc 0) (hGK 0) (fun j => horder 0 j (Nat.zero_le j))
    hpoint hvw hwc hwK (fun x => (hwB x).1)
  obtain ⟨a,ha,hKa⟩ := hK.isBounded.subset_ball_lt r (0 : Space n)
  have hKc : K ⊆ closedBall (0 : Space n) a := hKa.trans ball_subset_closedBall
  let L := ballGreen n (canonicalSphereArea n) (n : ℝ) a
  have hLc : Continuous L := continuous_ballGreen n _ _ (hr.trans ha)
  have hLv (x : Space n) : L x ≤ v x := by
    apply ge_of_tendsto (hpoint x)
    filter_upwards [hRlim.eventually (eventually_gt_atTop ‖x‖)] with j hj
    exact (hPDE j).ballGreen_lower_bound_on_critical_annulus hn hr ha.le hKc (hGc j)
      (fun y => (hB j y).1) (hout j) x (by simpa only [mem_ball,dist_zero_right] using hj)
  have hLe := leOn_of_ae_le_continuousOn_actual hK.isClosed.isOpen_compl hLc.continuousOn hwc (by
    filter_upwards [hvw] with x hx
    exact (hLv x).trans_eq hx)
  have hLw (x : Space n) : L x ≤ w x := by
    by_cases hx : x ∈ K
    · have hz : L x = 0 := ballGreen_zero_on_closedBall n _ _ a (hKc hx)
      rw [hz,hwK x hx]
    · exact hLe x hx
  let A := fundamentalRadialValue n (canonicalSphereArea n) (n : ℝ) a
  let B := fundamentalRadialValue n (canonicalSphereArea n) (n : ℝ) r
  have hrem : HasBoundedGreenRemainder n (canonicalSphereArea n) n w := by
    refine ⟨max |A| |B|, (abs_nonneg A).trans (le_max_left _ _), ?_⟩
    filter_upwards [eventually_ballGreen_remainder_eq n (canonicalSphereArea n) (n : ℝ) a,
      eventually_ballGreen_remainder_eq n (canonicalSphereArea n) (n : ℝ) r] with x hxa hxr
    have h1 := hLw x
    change ballGreen n (canonicalSphereArea n) (n : ℝ) a x ≤ w x at h1
    have h2 := (hwB x).2
    change ballGreen n (canonicalSphereArea n) (n : ℝ) a x - _ = -A at hxa
    change ballGreen n (canonicalSphereArea n) (n : ℝ) r x - _ = -B at hxr
    have hA := (le_abs_self A).trans (le_max_left |A| |B|)
    have hB' := (neg_le_abs B).trans (le_max_right |A| |B|)
    apply abs_le.mpr
    constructor <;> linarith only [h1,h2,hxa,hxr,hA,hB']
  exact ⟨w,g,⟨hn1,le_rfl,canonicalSphereArea_pos hn0,hK,hKne,hc,
    fun x hx => hwK x hx,⟨g,hwPDE⟩,hrem⟩,hwPDE,a,ha,hKc,fun x => ⟨hLw x,(hwB x).2⟩⟩

/-- Recenter on one interior ball, construct the solution there, and translate
it back with respect to the original canonical fundamental profile. -/
theorem existsUnique_critical_exterior_green_of_interior_tangent_balls
    {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty)
    (hballs : ∀ a ∈ K, ∃ z : Space n, ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ K ∧ dist a z = s) :
    ∃! w : Space n → ℝ, IsExteriorGreen n (canonicalSphereArea n) n K w := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨c,r,hr,hinner,_⟩ := hballs a ha
  let T : Space n → Space n := fun x => x-c
  let K' := T '' K
  have hK' : IsCompact K' := hK.image (continuous_id.sub continuous_const)
  have hinner' : closedBall (0 : Space n) r ⊆ K' := by
    intro x hx
    refine ⟨x+c,hinner ?_,add_sub_cancel_right x c⟩
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using hx
  have hballs' : ∀ y ∈ K', ∃ z : Space n, ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ K' ∧ dist y z = s := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨z,s,hs,hz,hxz⟩ := hballs x hx
    refine ⟨z-c,s,hs,?_,?_⟩
    · intro b hb
      refine ⟨b+c,hz ?_,add_sub_cancel_right b c⟩
      rw [mem_closedBall,dist_eq_norm] at hb ⊢
      rw [show b+c-z=b-(z-c) by abel]
      exact hb
    · change dist (x-c) (z-c) = s
      rw [dist_eq_norm,show x-c-(z-c)=x-z by abel,←dist_eq_norm]
      exact hxz
  obtain ⟨w,_,hw,_,_⟩ := exists_critical_exterior_green_with_concentric_bounds hn hK' hr hinner' hballs'
  have hback : (fun x : Space n => x+c) '' K' = K := by
    ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      simpa only [T,sub_add_cancel] using hz
    · intro hx
      exact ⟨x-c,⟨x,hx,rfl⟩,sub_add_cancel x c⟩
  have ht := hw.translate_actual c
  rw [hback] at ht
  exact ⟨_,ht,fun _ hg => hg.unique ht⟩

theorem existsUnique_critical_exterior_green_closedNeighborhood
    {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃! w : Space n → ℝ,
      IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood δ K) w := by
  obtain ⟨a,ha⟩ := hne
  have ha' : a ∈ BMCompact.closedNeighborhood δ K :=
    mem_cthickening_of_dist_le a a δ K ha (by simpa using hδ.le)
  exact existsUnique_critical_exterior_green_of_interior_tangent_balls hn
    (BMCompact.isCompact_closedNeighborhood hK δ) ⟨a,ha'⟩
    (closedNeighborhood_has_interior_tangent_balls (by omega) hK hδ)

end BMCompactPDE

#print axioms BMCompactPDE.exists_critical_exterior_green_with_concentric_bounds
#print axioms BMCompactPDE.existsUnique_critical_exterior_green_of_interior_tangent_balls
#print axioms BMCompactPDE.existsUnique_critical_exterior_green_closedNeighborhood
