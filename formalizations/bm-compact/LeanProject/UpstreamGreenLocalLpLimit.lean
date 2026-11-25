import WeakPDE
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! One actual raw field is constructed from Cauchy Lp data on a countable
increasing exhaustion. Local complete-space limits agree almost everywhere
on overlaps; a least-window selector glues their raw representatives. The
Cauchy property is an explicit input, not a consequence asserted here for a
particular Green family. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_actual_local_Lp_limit_of_cauchy_exhaustion
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω : Set (Space n)}
    (D : ℕ → Set (Space n)) (hD : ∀ m,MeasurableSet (D m))
    (hmono : Monotone D) (hcover : (⋃ m,D m)=Ω)
    (F : ℕ → Space n → Space n)
    (hMem : ∀ j m,MemLp (F j) (ENNReal.ofReal p) (volume.restrict (D m)))
    (hCauchy :
      letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
      ∀ m,CauchySeq (fun j=>(hMem j m).toLp (F j))) :
    ∃ g : Space n → Space n,∀ m,
      MemLp g (ENNReal.ofReal p) (volume.restrict (D m)) ∧
      Tendsto (fun j=>eLpNorm (F j-g) (ENNReal.ofReal p) (volume.restrict (D m)))
        atTop (𝓝 0) := by
  classical
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let μ : ℕ → Measure (Space n) := fun m=>volume.restrict (D m)
  let L (m j : ℕ) : Lp (Space n) q (μ m) := (hMem j m).toLp (F j)
  have hex (m : ℕ) : ∃ v : Lp (Space n) q (μ m),Tendsto (L m) atTop (𝓝 v) :=
    cauchySeq_tendsto_of_complete (hCauchy m)
  choose v hv using hex
  let G : ℕ → Space n → Space n := fun m=>(v m : Space n → Space n)
  have hG (m : ℕ) : MemLp (G m) q (μ m) := Lp.memLp (v m)
  have hlim (m : ℕ) :
      Tendsto (fun j=>eLpNorm (F j-G m) q (μ m)) atTop (𝓝 0) := by
    have hl := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (L m) (v m)).mp (hv m)
    apply hl.congr'
    apply Eventually.of_forall
    intro j
    exact eLpNorm_congr_ae ((hMem j m).coeFn_toLp.sub EventuallyEq.rfl)
  have hcompat_le (m k : ℕ) (hmk : m≤k) : G m=ᵐ[μ m] G k := by
    have hμ : μ m≤μ k := Measure.restrict_mono (hmono hmk) le_rfl
    have hGk : MemLp (G k) q (μ m) := (hG k).mono_measure hμ
    have hlimk : Tendsto (fun j=>eLpNorm (F j-G k) q (μ m)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim k)
        (fun _=>bot_le) (fun j=>eLpNorm_mono_measure (F j-G k) hμ)
    have hm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F (fun j=>hMem j m) (G m) (hG m)).mpr (hlim m)
    have hk := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F (fun j=>hMem j m) (G k) hGk).mpr hlimk
    have heq : (hG m).toLp (G m)=hGk.toLp (G k) := tendsto_nhds_unique hm hk
    calc
      G m=ᵐ[μ m] ((hG m).toLp (G m) : Space n → Space n) := (hG m).coeFn_toLp.symm
      _=ᵐ[μ m] (hGk.toLp (G k) : Space n → Space n) := by rw [heq]
      _=ᵐ[μ m] G k := hGk.coeFn_toLp
  have hcompat (m k : ℕ) :
      ∀ᵐ x ∂volume,x∈D m → x∈D k → G m x=G k x := by
    rcases le_total m k with hmk|hkm
    · filter_upwards [ae_imp_of_ae_restrict (hcompat_le m k hmk)] with x hx
      intro hxm _
      exact hx hxm
    · filter_upwards [ae_imp_of_ae_restrict (hcompat_le k m hkm)] with x hx
      intro _ hxk
      exact (hx hxk).symm
  have hall : ∀ᵐ x ∂volume,∀ m k,x∈D m → x∈D k → G m x=G k x :=
    ae_all_iff.mpr (fun m=>ae_all_iff.mpr (fun k=>hcompat m k))
  have hfind (x : Space n) (hx : x∈Ω) : ∃ m,x∈D m :=
    mem_iUnion.mp (hcover.symm ▸ hx)
  let g : Space n → Space n := fun x=>if hx : x∈Ω then G (Nat.find (hfind x hx)) x else 0
  have hg (m : ℕ) : g=ᵐ[μ m] G m := by
    apply (ae_restrict_iff' (hD m)).mpr
    filter_upwards [hall] with x hx
    intro hxm
    have hxΩ : x∈Ω := hcover ▸ mem_iUnion.mpr ⟨m,hxm⟩
    dsimp only [g]
    rw [dif_pos hxΩ]
    exact hx (Nat.find (hfind x hxΩ)) m (Nat.find_spec (hfind x hxΩ)) hxm
  refine ⟨g,fun m=>⟨(memLp_congr_ae (hg m)).mpr (hG m),?_⟩⟩
  apply (hlim m).congr'
  apply Eventually.of_forall
  intro j
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hg m).symm)

end BMCompactPDE
#print axioms BMCompactPDE.exists_actual_local_Lp_limit_of_cauchy_exhaustion
