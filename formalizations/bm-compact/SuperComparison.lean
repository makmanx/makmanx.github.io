import BMCompactChecked

/-! Genuine weak subsolution/supersolution comparison on relatively compact
bounded domains. The weak inequalities are actual flux integrals. The positive
part is an actual W0 test; the later C1 wrapper constructs it from frontier
order rather than assuming the desired comparison. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSubsolutionPair.mono {n : ℕ} {p : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hU : U ⊆ Ω) (hUopen : IsOpen U) :
    WeakPSubsolutionPair p U u g := by
  refine ⟨hu.1,hUopen,hu.2.2.1.mono hU,?_⟩
  intro D hD θ h hθ hnonneg
  exact hu.2.2.2 D ⟨hD.1,hD.2.1,hD.2.2.trans hU⟩ θ h hθ hnonneg

theorem WeakPSupersolutionPair.mono {n : ℕ} {p : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (hU : U ⊆ Ω) (hUopen : IsOpen U) :
    WeakPSupersolutionPair p U u g := by
  refine ⟨hu.1,hUopen,hu.2.2.1.mono hU,?_⟩
  intro D hD θ h hθ hnonneg
  exact hu.2.2.2 D ⟨hD.1,hD.2.1,hD.2.2.trans hU⟩ θ h hθ hnonneg

theorem WeakPSubsolutionPair.add_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (c : ℝ) :
    WeakPSubsolutionPair p Ω (fun x => u x+c) g :=
  ⟨hu.1,hu.2.1,hu.2.2.1.add_const hu.1 c,hu.2.2.2⟩

theorem WeakPSupersolutionPair.add_const {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSupersolutionPair p Ω u g) (c : ℝ) :
    WeakPSupersolutionPair p Ω (fun x => u x+c) g :=
  ⟨hu.1,hu.2.1,hu.2.2.1.add_const hu.1 c,hu.2.2.2⟩

/-- Actual weak inequalities force the gradient of an available positive
excess test to vanish; no comparison premise appears in the proof. -/
theorem WeakPSubsolutionPair.excess_gradient_ae_zero
    {n : ℕ} {p ε : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hv : WeakPSupersolutionPair p Ω v h)
    (hD : LocalDomain D Ω)
    (hpositive : ZeroBoundarySobolevPair p D
      (fun x => max (u x-v x-ε) 0)
      (fun x => if v x+ε<u x then g x-h x else 0)) :
    (fun x => if v x+ε<u x then g x-h x else 0) =ᵐ[volume.restrict D] 0 := by
  let θ : Space n → ℝ := fun x => max (u x-v x-ε) 0
  let w : Space n → Space n := fun x => if v x+ε<u x then g x-h x else 0
  have hθ : ZeroBoundarySobolevPair p D θ w := hpositive
  have hnonnegθ : ∀ᵐ x ∂volume.restrict D, 0≤θ x :=
    Eventually.of_forall (fun x => le_max_right _ _)
  obtain ⟨hgi,hgle⟩ := hu.2.2.2 D hD θ w hθ hnonnegθ
  obtain ⟨hhi,hhge⟩ := hv.2.2.2 D hD θ w hθ hnonnegθ
  let pairing : Space n → ℝ := fun x =>
    inner ℝ (pFlux p (g x)-pFlux p (h x)) (w x)
  have hpair : pairing = fluxPairing p g w-fluxPairing p h w := by
    funext x
    simp only [pairing,fluxPairing,Pi.sub_apply,inner_sub_left]
  have hpi : Integrable pairing (volume.restrict D) := by
    rw [hpair]
    exact hgi.sub hhi
  have hple : (∫ x in D, pairing x)≤0 := by
    rw [hpair]
    simp only [Pi.sub_apply]
    rw [integral_sub hgi hhi]
    linarith
  have hnonneg : 0≤ᵐ[volume.restrict D] pairing := by
    apply Eventually.of_forall
    intro x
    by_cases hx : v x+ε<u x
    · simp only [pairing,w,if_pos hx]
      exact pFlux_monotonicity hu.1 (g x) (h x)
    · simp only [pairing,w,if_neg hx,inner_zero_right]
      exact le_rfl
  have hpeq : (∫ x in D, pairing x)=0 :=
    le_antisymm hple (integral_nonneg_of_ae hnonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hpi).1 hpeq
  change w =ᵐ[volume.restrict D] 0
  filter_upwards [hzero] with x hx
  by_cases hpos : v x+ε<u x
  · have hgh : g x=h x :=
      (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).1 (by
        simpa only [pairing,w,if_pos hpos,Pi.zero_apply] using hx)
    simp only [w,if_pos hpos,hgh,sub_self,Pi.zero_apply]
  · simp only [w,if_neg hpos,Pi.zero_apply]

theorem WeakPSubsolutionPair.leOn_add_of_local_W0_excess
    {n : ℕ} {p ε : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hv : WeakPSupersolutionPair p Ω v h)
    (hD : LocalDomain D Ω) (hn : 2≤n)
    (hpositive : ZeroBoundarySobolevPair p D
      (fun x => max (u x-v x-ε) 0)
      (fun x => if v x+ε<u x then g x-h x else 0))
    (huc : ContinuousOn u D) (hvc : ContinuousOn v D) :
    ∀ x∈D, u x≤v x+ε := by
  have hw := hu.excess_gradient_ae_zero hv hD hpositive
  have hθc : ContinuousOn (fun x => max (u x-v x-ε) 0) D :=
    ((huc.sub hvc).sub continuousOn_const).sup continuousOn_const
  have hz := hpositive.eqOn_zero_of_gradient_ae_zero hn hD.1 hD.2.1 hw hθc
  intro x hx
  have hmax : max (u x-v x-ε) 0=0 := hz hx
  have hd : u x-v x-ε≤0 := (le_max_left _ _).trans hmax.le
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.mono
#print axioms BMCompactPDE.WeakPSupersolutionPair.mono
#print axioms BMCompactPDE.WeakPSubsolutionPair.add_const
#print axioms BMCompactPDE.WeakPSupersolutionPair.add_const
#print axioms BMCompactPDE.WeakPSubsolutionPair.excess_gradient_ae_zero
#print axioms BMCompactPDE.WeakPSubsolutionPair.leOn_add_of_local_W0_excess
