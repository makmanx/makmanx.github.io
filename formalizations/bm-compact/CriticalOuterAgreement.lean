import CriticalOuterLaws

/-! Critical Green capacity agrees with the outer capacity whenever the
original obstacle has an actual Green function and each positive neighbourhood
has finite Green data. Even the finite constant for the original Green
function is derived from these assumptions. -/
noncomputable section
open Set Filter Metric Bornology
open scoped Topology
namespace BMCompactPDE

/-- A bound on one Green function on a larger obstacle controls the entire
difference. This estimate uses only bounded remainders at infinity. -/
theorem IsExteriorGreen.le_add_of_nested_boundary {n : ℕ} {σ p b : ℝ}
    {K L : Set (Space n)} {G H : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) (hH : IsExteriorGreen n σ p L H)
    (hKL : K ⊆ L) (hb : ∀ x ∈ L, G x ≤ b) :
    ∀ x, G x ≤ H x + b := by
  have hinf := hH.tendsto_atTop_at_infinity
  obtain ⟨hn,_,_,_,_,hGc,_,⟨g,hg⟩,C,_,hC⟩ := hG
  obtain ⟨_,_,_,hL,_,hHc,hH0,⟨h,hh⟩,D,_,hD⟩ := hH
  have hn' : 1 < n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  have hg' := hg.mono (compl_subset_compl.mpr hKL) hL.isClosed.isOpen_compl
  have hs (α : ℝ) (hα : 0 < α) (x : Space n) : G x ≤ ((1+α) • H) x + b := by
    have hbd (y : Space n) (hy : y ∈ L) : G y ≤ ((1+α) • H) y + b := by
      simpa only [Pi.smul_apply,hH0 hy,smul_zero,zero_add] using hb y hy
    by_cases hx : x ∈ L
    · exact hbd x hx
    · apply hg'.leOn_compl_of_continuous_boundary_order_and_infinity_order hL hn2
        ((hh.smul (1+α)).add_const b) hGc ((continuous_const.smul hHc).add continuous_const) hbd _ x hx
      intro η hη
      rw [← Metric.cobounded_eq_cocompact]
      filter_upwards [hC,hD,hinf.eventually (eventually_ge_atTop ((C+D-b)/α))] with y hyC hyD hy
      have hmul := (div_le_iff₀ hα).mp hy
      change G y - ((1+α)*H y + b) < η
      nlinarith only [(abs_le.mp hyC).2,(abs_le.mp hyD).1,hmul,hη]
  intro x
  have ht : Tendsto (fun α : ℝ => (1+α)*H x + b) (𝓝[>] 0) (𝓝 (H x+b)) := by
    have hc : Continuous (fun α : ℝ => (1+α)*H x + b) := by fun_prop
    have he : Tendsto (fun α : ℝ => (1+α)*H x + b) (𝓝[>] 0) (𝓝 ((1+0)*H x + b)) :=
      hc.continuousAt.continuousWithinAt.tendsto
    simpa only [add_zero,one_mul] using he
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact hs α hα x

/-- Theorem B(b) from actual neighbourhood Green capacities. The limits of
the neighbourhood capacities and of G−F at infinity are both constructed. -/
theorem IsExteriorGreen.exists_asymptotic_and_criticalOuterCapacity {n : ℕ} {σ : ℝ}
    {K : Set (Space n)} {G : Space n → ℝ} (hG : IsExteriorGreen n σ n K G)
    (hneigh : ∀ δ : ℝ, 0 < δ →
      ∃ c, HasCriticalGreenCapacity σ (BMCompact.closedNeighborhood δ K) c) :
    ∃ k : ℝ, HasGreenAsymptotic n σ n G k ∧
      HasCriticalOuterCapacity σ K (greenCapacityOfConstant n σ n k) := by
  classical
  have hn' : 1 < n := by exact_mod_cast hG.1
  have : NeZero n := ⟨by omega⟩
  have hK := hG.2.2.2.1
  have hGc := hG.2.2.2.2.2.1
  have hG0 := hG.2.2.2.2.2.2.1
  obtain ⟨C,_,hC⟩ := hG.2.2.2.2.2.2.2.2
  have hw (δ : ℝ) : ∃ (H : Space n → ℝ) (l : ℝ), 0 < δ →
      IsExteriorGreen n σ n (BMCompact.closedNeighborhood δ K) H ∧
      HasGreenAsymptotic n σ n H l := by
    by_cases hδ : 0 < δ
    · obtain ⟨_,H,l,hH,hl,_⟩ := hneigh δ hδ
      exact ⟨H,l,fun _ => ⟨hH,hl⟩⟩
    · exact ⟨0,0,fun h => (hδ h).elim⟩
  choose H k hk using hw
  have sub (δ : ℝ) := BMCompact.subset_closedNeighborhood K δ
  have hle (δ : ℝ) (hδ : 0 < δ) : H δ ≤ G :=
    hG.antitone_obstacle (hk δ hδ).1 (sub δ)
  have hanti : AntitoneOn k (Ioi (0:ℝ)) := by
    intro δ hδ ε hε hd
    exact (hk δ hδ).1.asymptotic_constant_antitone_obstacle (hk ε hε).1
      (BMCompact.closedNeighborhood_mono K hd) (hk δ hδ).2 (hk ε hε).2
  have hb : BddAbove (k '' Ioi (0:ℝ)) := by
    refine ⟨C,?_⟩
    rintro _ ⟨δ,hδ,rfl⟩
    apply le_of_tendsto (hk δ hδ).2
    filter_upwards [hC] with x hx
    exact (sub_le_sub_right (hle δ hδ x) _).trans (abs_le.mp hx).2
  let kLimit := sSup (k '' Ioi (0:ℝ))
  have hlim : Tendsto k (𝓝[>] (0:ℝ)) (𝓝 kLimit) := hanti.tendsto_nhdsGT hb
  refine ⟨kLimit,?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hthird : 0 < ε/3 := by linarith
    have hsmall : K ⊆ {x | G x < ε/3} := by
      intro x hx
      change G x < ε/3
      simpa only [hG0 hx] using hthird
    obtain ⟨d,hd,hds⟩ := hK.exists_cthickening_subset_open
      (isOpen_lt hGc continuous_const) hsmall
    have hclose := Metric.tendsto_nhds.mp hlim (ε/3) hthird
    obtain ⟨δ,hδk,hδ⟩ := (hclose.and (Ioo_mem_nhdsGT hd)).exists
    have herror := hG.le_add_of_nested_boundary (hk δ hδ.1).1 (sub δ)
      (fun x hx => (hds ((cthickening_mono hδ.2.le K) hx)).le)
    have hlimδ := Metric.tendsto_nhds.mp (hk δ hδ.1).2 (ε/3) hthird
    filter_upwards [hlimδ] with x hx
    rw [Real.dist_eq] at hx hδk ⊢
    obtain ⟨hl,hu⟩ := abs_lt.mp hx
    obtain ⟨hl',hu'⟩ := abs_lt.mp hδk
    exact abs_lt.mpr ⟨by linarith only [hl,hl',hle δ hδ.1 x,hε],
      by linarith only [hu,hu',herror x]⟩
  · refine ⟨fun δ => greenCapacityOfConstant n σ n (k δ),?_,?_⟩
    · intro δ hδ
      exact ⟨H δ,k δ,(hk δ hδ).1,(hk δ hδ).2,rfl⟩
    · simp only [greenCapacityOfConstant,ite_true]
      exact Real.continuous_exp.continuousAt.tendsto.comp (hlim.neg.div_const _)

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.le_add_of_nested_boundary
#print axioms BMCompactPDE.IsExteriorGreen.exists_asymptotic_and_criticalOuterCapacity
