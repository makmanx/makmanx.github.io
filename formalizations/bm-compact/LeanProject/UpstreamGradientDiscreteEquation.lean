import UpstreamGradientMeanJacobian

/-! Genuine finite-difference linearized weak equations. The coefficient is
the actual averaged Jacobian between the supplied weak-gradient values.
Actual translation and full-W0 testing cancel the constant source. The
function and its weak gradient are the actual scalar/gradient quotients.
This is a finite-difference equation, not a derivative-level chain rule. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

def regularizedSpatialCoefficient {n : ℕ} (p ε : ℝ)
    (g : Space n → Space n) (a : Space n) (x : Space n) : Space n →L[ℝ] Space n :=
  regularizedMeanJacobian p ε (g (x+a)) (g x)

/-- Every actual spatial quotient solves a genuine linear divergence-form
weak equation with its constructed averaged-Jacobian coefficient, against
all actual W0 tests on the overlap domain. No differentiability, Hessian,
gradient bound or coefficient equation is an input. -/
theorem GlobalWeakRegularizedSourcePair.discrete_linearized_weak_equation
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g) (hε : ε≠0)
    (a : Space n) (t : ℝ) :
    let O := Ω∩((fun x : Space n => x+a) ⁻¹' Ω)
    let z := fun x => t⁻¹*(u (x+a)-u x)
    let G := fun x => t⁻¹ • (g (x+a)-g x)
    SobolevPair p O z G ∧
      ∀ θ : Space n → ℝ,∀ k : Space n → Space n,
        ZeroBoundarySobolevPair p O θ k →
        Integrable (fun x => inner ℝ (regularizedSpatialCoefficient p ε g a x (G x)) (k x))
          (volume.restrict O) ∧
        (∫ x in O,inner ℝ (regularizedSpatialCoefficient p ε g a x (G x)) (k x))=0 := by
  dsimp only
  let O := Ω∩((fun x : Space n => x+a) ⁻¹' Ω)
  have hO : IsOpen O := hu.2.1.inter (hu.2.1.preimage (continuous_id.add continuous_const))
  have hU := hu.mono_actual inter_subset_left hO
  have hV := (hu.translate_actual a).mono_actual inter_subset_right hO
  have hs : SobolevPair p O ((fun x => u (x+a))-u) ((fun x => g (x+a))-g) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using hV.2.2.1.add (hU.2.2.1.smul (-1))
  refine ⟨?_,?_⟩
  · simpa only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul] using! hs.smul t⁻¹
  intro θ k hθ
  obtain ⟨hVI,hVE⟩ := hV.2.2.2 θ k hθ
  obtain ⟨hUI,hUE⟩ := hU.2.2.2 θ k hθ
  have heq :
      (fun x => inner ℝ (regularizedSpatialCoefficient p ε g a x
        (t⁻¹ • (g (x+a)-g x))) (k x))=
      (fun x => t⁻¹*(inner ℝ ((ε^2+‖g (x+a)‖^2)^((p-2)/2) • g (x+a)) (k x)-
        inner ℝ ((ε^2+‖g x‖^2)^((p-2)/2) • g x) (k x))) := by
    funext x
    rw [regularizedSpatialCoefficient,map_smul,regularizedMeanJacobian_apply_sub p hε,
      real_inner_smul_left,inner_sub_left]
  rw [heq]
  refine ⟨(hVI.sub hUI).const_mul t⁻¹,?_⟩
  rw [integral_const_mul,integral_sub hVI hUI,hVE,hUE,sub_self,mul_zero]

end BMCompactPDE
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.discrete_linearized_weak_equation
