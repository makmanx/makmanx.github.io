import UpstreamMorreyEstimate
import RootLpMollification
import RootWeakMollification
import RootEssentialRepresentative
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Genuine global Morrey representatives for the actual Sobolev graph.
The dense-set selection helper and the original weak-Morrey method are
attributed to Mazecto's accepted Prove2Me proofs; source records are retained.
The actual normalized smooth approximants and their norm bounds are derived
from the independent supplied weak gradient using the native graph, not an
imported Hunter weak-derivative definition or regularity assumption. -/
noncomputable section
set_option autoImplicit false
section MorreySelectionReuse

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

private theorem morrey_ae_limit_representative {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (K : ℝ≥0) (α : ℝ) (hα : 0 < α) (v : ℕ → X → Y) (f : X → Y)
    (hv : ∀ j x y, dist (v j x) (v j y) ≤ (K : ℝ) * dist x y ^ α)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => v j x) atTop (𝓝 (f x))) :
    ∃ u : X → Y, Continuous u ∧ u =ᵐ[μ] f ∧
      ∀ x y, dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ α := by
  classical
  let s : Set X := {x | Tendsto (fun j => v j x) atTop (𝓝 (f x))}
  have hs : Dense s := μ.dense_of_ae hf
  have hbound (x : s) (y : s) :
      dist (f x) (f y) ≤ (K : ℝ) * dist (x : X) (y : X) ^ α :=
    le_of_tendsto (x.property.dist y.property) (Eventually.of_forall fun j => hv j x y)
  have hholder : HolderWith K ⟨α, hα.le⟩ (fun x : s => f x) := by
    intro x y
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (dist (x : X) (y : X)) ^ α
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    simpa only [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      using ENNReal.ofReal_le_ofReal (hbound x y)
  have huc : UniformContinuous (fun x : s => f x) := hholder.uniformContinuous hα
  let u : X → Y := hs.extend (fun x : s => f x)
  have hu : Continuous u := (hs.uniformContinuous_extend huc).continuous
  have heq (x : s) : u x = f x := hs.extend_of_ind huc x
  refine ⟨u, hu, hf.mono (fun x hx => heq ⟨x, hx⟩), ?_⟩
  intro x y
  apply hs.induction (P := fun x => dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ α) _ _ x
  · intro a ha
    apply hs.induction (P := fun y => dist (u a) (u y) ≤ (K : ℝ) * dist a y ^ α) _ _ y
    · intro b hb
      simpa only [heq ⟨a, ha⟩, heq ⟨b, hb⟩] using hbound ⟨a, ha⟩ ⟨b, hb⟩
    · exact isClosed_le (continuous_const.dist hu)
        (continuous_const.mul ((continuous_const.dist continuous_id).rpow_const (fun _ => Or.inr hα.le)))
  · exact isClosed_le (hu.dist continuous_const)
      (continuous_const.mul ((continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr hα.le)))

end MorreySelectionReuse
open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace BMCompactPDE

/-- The actual global Sobolev graph has a quantitative continuous Morrey
representative above the dimension. No representative or bound is an input.
The constant is chosen before the scalar and supplied weak-gradient field. -/
theorem exists_actual_global_morrey_constant {n : ℕ} {p : ℝ}
    (hn : 1≤n) (hnp : (n:ℝ)<p) :
    ∃ A : ℝ≥0,∀ (f : Space n → ℝ) (g : Space n → Space n),
      SobolevPair p univ f g →
      ∃ u : Space n → ℝ,Continuous u ∧ f =ᵐ[volume] u ∧
        ∀ x y,dist (u x) (u y)≤(A:ℝ)*(eLpNorm g (ENNReal.ofReal p) volume).toReal*
          dist x y^(1-(n:ℝ)/p) := by
  classical
  obtain ⟨A,hA⟩ := BMCompactMorreyReuse.morrey_increment_of_contDiff hnp
  refine ⟨A,fun f g hf => ?_⟩
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hf.1.le
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hfm : MemLp f q volume := by simpa only [q,Measure.restrict_univ] using hf.2.1
  have hgm : MemLp g q volume := by simpa only [q,Measure.restrict_univ] using hf.2.2.1
  let N : ℝ≥0 := (eLpNorm g q volume).toNNReal
  have hN : (N:ℝ≥0∞)=eLpNorm g q volume := by
    exact ENNReal.coe_toNNReal hgm.eLpNorm_ne_top
  let φ : ℕ → ContDiffBump (0 : Space n) := fun j =>
    {rIn := (1/((j:ℝ)+1))/2
     rOut := 1/((j:ℝ)+1)
     rIn_pos := by positivity
     rIn_lt_rOut := half_lt_self (by positivity)}
  let v : ℕ → Space n → ℝ := fun j => normalizedMollify (φ j) f
  have hv (j : ℕ) : ContDiff ℝ ∞ (v j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ j).contDiff_normed (hfm.locallyIntegrable hq)
  have hcomm (j : ℕ) : gradient (v j)=normalizedMollify (φ j) g :=
    hf.gradient_convolution_eq (φ j).contDiff_normed (φ j).hasCompactSupport_normed
  have hgrad (j : ℕ) : eLpNorm (fun z => ‖gradient (v j) z‖) q volume≤(N:ℝ≥0∞) := by
    rw [eLpNorm_norm,hcomm,hN]
    exact eLpNorm_convolution_le_vector hq hqt (φ j).continuous_normed
      (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hgm
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hae : ∀ᵐ x ∂volume,Tendsto (fun j => v j x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
      (.of_forall (fun j => show (φ j).rOut≤2*(φ j).rIn by dsimp [φ];linarith))
      (hfm.locallyIntegrable hq)
  have hp : 0<p := lt_of_lt_of_le zero_lt_one hf.1.le
  have hα : 0<1-(n:ℝ)/p := sub_pos.mpr ((div_lt_one hp).mpr hnp)
  have hbound (j : ℕ) (x y : Space n) :
      dist (v j x) (v j y)≤((A*N:ℝ≥0):ℝ)*dist x y^(1-(n:ℝ)/p) := by
    have hb : ENNReal.ofReal |v j x-v j y|≤
        (A:ℝ≥0∞)*(N:ℝ≥0∞)*ENNReal.ofReal (‖x-y‖^(1-(n:ℝ)/p)) := by
      apply (hA (v j) ((hv j).of_le (by norm_num)) x y).trans
      gcongr
      exact hgrad j
    have hr : |v j x-v j y|≤(A:ℝ)*(N:ℝ)*‖x-y‖^(1-(n:ℝ)/p) := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      simpa only [ENNReal.ofReal_mul (mul_nonneg A.coe_nonneg N.coe_nonneg),
        ENNReal.ofReal_mul A.coe_nonneg,ENNReal.ofReal_coe_nnreal] using hb
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,NNReal.coe_mul] using hr
  obtain ⟨u,huc,huf,hu⟩ := morrey_ae_limit_representative volume (A*N)
    (1-(n:ℝ)/p) hα v f hbound hae
  refine ⟨u,huc,huf.symm,?_⟩
  intro x y
  have hh := hu x y
  change dist (u x) (u y)≤(A:ℝ)*(N:ℝ)*dist x y^(1-(n:ℝ)/p) at hh
  exact hh

end BMCompactPDE
#print axioms BMCompactPDE.exists_actual_global_morrey_constant
