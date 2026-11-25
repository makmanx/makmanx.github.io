import GreenFilling

noncomputable section
set_option autoImplicit false
open Set
open scoped Pointwise
namespace BMCompactPDE

theorem fillBoundedHoles_idempotent {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) : fillBoundedHoles (fillBoundedHoles K) = fillBoundedHoles K := by
  obtain ⟨_,_,hG,_⟩ := exists_canonical_exterior_green_supercritical_nonempty
    (p := (n:ℝ)+1) hn (lt_add_one _) hK hne
  exact hG.on_filled.fill_eq_zero_set.trans hG.fill_eq_zero_set.symm

/-- A nonzero affine homothety taking one obstacle into another takes its
filled set into the other filled set. The inverse sends exterior components
into exterior components and the forward map preserves their boundedness. -/
theorem affine_mapsTo_filled {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) (a : Space n)
    {K L : Set (Space n)} (h : MapsTo (fun x => ρ • x+a) K L) :
    MapsTo (fun x => ρ • x+a) (fillBoundedHoles K) (fillBoundedHoles L) := by
  let f : Space n → Space n := fun x => ρ • x+a
  let g : Space n → Space n := fun y => ρ⁻¹ • (y-a)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgf (x : Space n) : g (f x) = x := by simp [f,g,smul_smul,hρ]
  have hfg (x : Space n) : f (g x) = x := by simp [f,g,smul_smul,hρ]
  intro x hx
  change f x ∈ fillBoundedHoles L
  by_cases hy : f x ∈ L
  · exact Or.inl hy
  rcases hx with hx | ⟨_,hb⟩
  · exact False.elim (hy (h hx))
  refine Or.inr ⟨hy,?_⟩
  have hinc : g '' Lᶜ ⊆ Kᶜ := by
    rintro _ ⟨z,hz,rfl⟩ hk
    have hh : f (g z) ∈ L := h hk
    exact hz (hfg z ▸ hh)
  have hcomp := hg.continuousOn.image_connectedComponentIn_subset (s:=Lᶜ) (a:=f x) hy
  have hback : g '' connectedComponentIn Lᶜ (f x) ⊆ connectedComponentIn Kᶜ x := by
    have hh := hcomp.trans (connectedComponentIn_mono (g (f x)) hinc)
    rwa [hgf] at hh
  apply (hb.isCompact_closure.image hf).isBounded.subset
  intro y hy'
  exact ⟨g y,subset_closure (hback ⟨y,hy',rfl⟩),hfg y⟩

/-- Weighted sums of the filled inputs lie in the filling of the weighted
sum of the original compact obstacles, even for nonconvex inputs. -/
theorem smul_fill_add_smul_fill_subset {n : ℕ} (hn : 2 ≤ n) {K L : Set (Space n)}
    (hK : IsCompact K) (hL : IsCompact L) (hne : K.Nonempty) (hne' : L.Nonempty)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t • fillBoundedHoles K + (1-t) • fillBoundedHoles L ⊆ fillBoundedHoles (t • K + (1-t) • L) := by
  let S := t • K + (1-t) • L
  have hS : IsCompact S := (hK.smul t).add (hL.smul (1-t))
  have hs : S.Nonempty := (hne.image _).add (hne'.image _)
  have hleft (y : Space n) (hy : y ∈ L) :
      MapsTo (fun x => t • x + (1-t) • y) (fillBoundedHoles K) (fillBoundedHoles S) :=
    affine_mapsTo_filled ht.ne' _ (fun x hx => ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩)
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  have hr : MapsTo (fun z => (1-t) • z + t • x) L (fillBoundedHoles S) := by
    intro z hz
    simpa only [add_comm] using hleft z hz hx
  have hh := affine_mapsTo_filled (sub_pos.mpr ht1).ne' _ hr hy
  rw [fillBoundedHoles_idempotent hn hS hs] at hh
  simpa only [add_comm] using hh

end BMCompactPDE
#print axioms BMCompactPDE.fillBoundedHoles_idempotent
#print axioms BMCompactPDE.affine_mapsTo_filled
#print axioms BMCompactPDE.smul_fill_add_smul_fill_subset
