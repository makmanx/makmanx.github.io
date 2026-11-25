import RootEssentialRepresentative

/-! Pure sequence decay and interval-to-representative plumbing.  The PDE
must derive the actual interval bounds and recurrence; these hypotheses are
explicit here and are not substituted for a weak regularity proof. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace BMCompactRegularity

theorem tendsto_zero_of_max_contraction {q : ℝ} (hq0 : 0≤q) (hq1 : q<1)
    {w F : ℕ → ℝ} (hw : ∀ j,0≤w j) (hF : Tendsto F atTop (𝓝 0))
    (hstep : ∀ j,w (j+1)≤max (q*w j) (F j)) :
    Tendsto w atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0<ε/2 := by linarith
  have hhalfε : ε/2<ε := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hF.eventually (gt_mem_nhds hhalf))
  have hupper (k : ℕ) : w (N+k)≤max (q^k*w N) (ε/2) := by
    induction k with
    | zero => simpa only [Nat.add_zero,pow_zero,one_mul] using (le_max_left (w N) (ε/2))
    | succ k hk =>
      have hmul : q*max (q^k*w N) (ε/2)≤max (q^(k+1)*w N) (ε/2) := by
        rcases le_total (q^k*w N) (ε/2) with h|h
        · rw [max_eq_right h]
          have he := mul_le_mul_of_nonneg_right hq1.le hhalf.le
          have he' : q*(ε/2)≤ε/2 := by simpa only [one_mul] using he
          exact he'.trans (le_max_right _ _)
        · rw [max_eq_left h]
          have he : q*(q^k*w N)=q^(k+1)*w N := by rw [pow_succ];ring
          rw [he]
          exact le_max_left _ _
      have hindex : N≤N+k := Nat.le_add_right _ _
      have hs := hstep (N+k)
      have hb : max (q*w (N+k)) (F (N+k))≤max (q^(k+1)*w N) (ε/2) :=
        max_le ((mul_le_mul_of_nonneg_left hk hq0).trans hmul)
          ((hN _ hindex).le.trans (le_max_right _ _))
      simpa only [Nat.add_assoc,Nat.succ_eq_add_one] using hs.trans hb
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (w N)
  simp only [zero_mul] at hp
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds hhalf))
  refine ⟨N+K,?_⟩
  intro j hj
  have hNj : N≤j := (Nat.le_add_right N K).trans hj
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hNj
  have hk : K≤k := Nat.le_of_add_le_add_left hj
  have hv : w (N+k)<ε := (hupper k).trans_lt
    (max_lt ((hK k hk).trans hhalfε) hhalfε)
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hw (N+k))] using hv

end BMCompactRegularity
namespace BMCompactRepresentative
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]

theorem vanishingEssentialOscillation_of_interval_sequences {u : X → ℝ} {Ω : Set X}
    (h : ∀ x ∈ Ω,∃ (r lo hi : ℕ → ℝ),
      (∀ j,0<r j) ∧ (∀ j,Metric.ball x (r j)⊆Ω) ∧
      (∀ j,∀ᵐ y ∂μ.restrict (Metric.ball x (r j)),lo j≤u y ∧ u y≤hi j) ∧
      Tendsto (fun j => hi j-lo j) atTop (𝓝 0)) :
    VanishingEssentialOscillation μ u Ω := by
  intro x hx ε hε
  obtain ⟨r,lo,hi,hr,hsub,hae,hlim⟩ := h x hx
  obtain ⟨j,hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨Metric.ball x (r j),lo j,isOpen_ball,mem_ball_self (hr j),hsub j,?_⟩
  filter_upwards [hae j] with y hy
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.1)]
  linarith [hy.2,hj]

end BMCompactRepresentative
#print axioms BMCompactRegularity.tendsto_zero_of_max_contraction
#print axioms BMCompactRepresentative.vanishingEssentialOscillation_of_interval_sequences
