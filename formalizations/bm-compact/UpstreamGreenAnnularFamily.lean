import UpstreamGreenAnnularConstruction

/-! A genuinely constructed canonical supercritical annular family, with radii
increasing to infinity. Radius comparison is proved on the smaller ball only;
outside both balls the constant boundary values need not decrease. No family,
order, bound, trace or approximation premise is supplied. No limit is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem annular_radius_order {n : ℕ} {p R S : ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hn : 2≤n) (hRS : R≤S)
    {G H : Space n → ℝ} {g h : Space n → Space n}
    (hGc : Continuous G) (hHc : Continuous H)
    (hGK : ∀ x∈K,G x=0) (hHK : ∀ x∈K,H x=0)
    (hGout : ∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) p R)
    (hG : WeakPHarmonicPair p (ball 0 R\K) G g)
    (hH : WeakPHarmonicPair p (ball 0 S\K) H h)
    (hHF : ∀ x,H x≤fundamentalPotential n (canonicalSphereArea n) p x) :
    ∀ x∈ball 0 R,H x≤G x := by
  have hD : IsOpen (ball (0 : Space n) R\K) := isOpen_ball.sdiff hK.isClosed
  have hDb : Bornology.IsBounded (ball (0 : Space n) R\K) := isBounded_ball.subset sdiff_subset
  have hDS : (ball (0 : Space n) R\K)⊆(ball (0 : Space n) S\K) :=
    fun _ hx=>⟨ball_subset_ball hRS hx.1,hx.2⟩
  have hboundary : ∀ y∈frontier (ball (0 : Space n) R\K),H y≤G y := by
    intro y hy
    by_cases hyK : y∈K
    · rw [hGK y hyK,hHK y hyK]
    · have hyn : y∉ball (0 : Space n) R := fun hyB=>(hD.frontier_eq ▸ hy).2 ⟨hyB,hyK⟩
      have hyclosed : y∈closedBall (0 : Space n) R := closure_ball_subset_closedBall
        ((closure_mono (sdiff_subset : (ball (0 : Space n) R\K)⊆ball 0 R)) (frontier_subset_closure hy))
      have hynorm : ‖y‖=R := le_antisymm
        (by simpa only [mem_closedBall,dist_zero_right] using hyclosed)
        (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hyn))
      have hF : fundamentalPotential n (canonicalSphereArea n) p y=fundamentalRadialValue n (canonicalSphereArea n) p R := by
        rw [←fundamentalPotential_norm,hynorm]
      rw [hGout y hyn]
      exact (hHF y).trans_eq hF
  have hcmp := (hH.mono hDS hD).leOn_of_bounded_continuous_boundary_order hn hDb hG
    hHc.continuousOn hGc.continuousOn hboundary
  intro x hx
  by_cases hxK : x∈K
  · rw [hGK x hxK,hHK x hxK]
  · exact hcmp x ⟨hx,hxK⟩

set_option maxHeartbeats 1200000 in
theorem exists_canonical_annular_green_family_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p) {K : Set (Space n)} (hK : IsCompact K)
    (h0 : (0 : Space n)∈K) :
    ∃ R : ℕ → ℝ,∃ G : ℕ → Space n → ℝ,∃ Γ : ℕ → Space n → Space n,
      (∀ j,0<R j ∧ K⊆ball 0 (R j)) ∧ StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ j,Continuous (G j)) ∧ (∀ j x,x∈K → G j x=0) ∧
      (∀ j x,x∉ball 0 (R j) → G j x=fundamentalRadialValue n (canonicalSphereArea n) p (R j)) ∧
      (∀ j,MemLp (Γ j) (ENNReal.ofReal p) volume) ∧
      (∀ j B,Bornology.IsBounded B → SobolevPair p B (G j) (Γ j)) ∧
      (∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (Γ j)) ∧
      (∀ j x,0≤G j x ∧ G j x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      (∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) ∧
      ∀ i,∃ u : Space n → ℝ,∃ g : Space n → Space n,
        Continuous u ∧ (∀ x∈K,u x=1) ∧ (∀ x∉ball 0 (R i),u x=0) ∧ (∀ x,0≤u x ∧ u x≤1) ∧
        ZeroBoundarySobolevPair p (ball 0 (R i)) u g ∧ SobolevPair p univ u g ∧
        BMCompactCapacityV2.relativeCapacity p K (ball 0 (R i))=ENNReal.ofReal (∫ x in ball 0 (R i),‖g x‖^p ∂volume) ∧
        (∀ x,G i x=fundamentalRadialValue n (canonicalSphereArea n) p (R i)*(1-u x)) ∧
        (∀ x,Γ i x=(-fundamentalRadialValue n (canonicalSphereArea n) p (R i)) • g x) ∧
        ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K (ball 0 (R i)) (φ j)) ∧
          Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
          Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  classical
  obtain ⟨A,hA,hKA⟩ := hK.isBounded.subset_ball_lt 1 (0 : Space n)
  let R : ℕ → ℝ := fun j=>A+(j:ℝ)
  have hR (j : ℕ) : 0<R j := by
    have hA0 : 0<A := zero_lt_one.trans hA
    exact hA0.trans_le (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hKR (j : ℕ) : K⊆ball 0 (R j) := hKA.trans
    (ball_subset_ball (le_add_of_nonneg_right (Nat.cast_nonneg j)))
  have hRmono : StrictMono R := by
    intro j k hjk
    have hcast : (j:ℝ)<(k:ℝ) := by exact_mod_cast hjk
    change A+(j:ℝ)<A+(k:ℝ)
    linarith only [hcast]
  have hRlim : Tendsto R atTop atTop := by
    simpa only [R] using tendsto_atTop_add_const_left atTop A tendsto_natCast_atTop_atTop
  choose G Γ hGc hGK hGout hΓ hSob hH hB hPayload using
    (fun j=>exists_canonical_annular_green_approximant_supercritical hn hnp hK h0 (hR j) (hKR j))
  have horder (j k : ℕ) (hjk : j≤k) : ∀ x∈ball 0 (R j),G k x≤G j x :=
    annular_radius_order hK hn (hRmono.monotone hjk) (hGc j) (hGc k) (hGK j) (hGK k)
      (hGout j) (hH j) (hH k) (fun x=>(hB k x).2)
  exact ⟨R,G,Γ,(fun j=>⟨hR j,hKR j⟩),hRmono,hRlim,hGc,hGK,hGout,hΓ,hSob,hH,hB,horder,hPayload⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_annular_green_family_supercritical
