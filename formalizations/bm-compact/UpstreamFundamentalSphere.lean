import BMCompactChecked
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! A concrete normalization constant obtained from Euclidean volume's actual
polar sphere measure. It is not a free positive parameter. Identification with
an independently defined Hausdorff surface measure is not asserted here. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Metric
open scoped ENNReal
namespace BMCompactPDE

def canonicalSphereArea (n : ℕ) : ℝ :=
  (volume : Measure (Space n)).toSphere.real univ

/-- The actual polar sphere mass equals dimension times unit-ball volume. -/
theorem canonicalSphereArea_eq_unitBall (n : ℕ) :
    canonicalSphereArea n = (n : ℝ) * volume.real (ball (0 : Space n) 1) := by
  simpa only [canonicalSphereArea,Space,finrank_euclideanSpace,Fintype.card_fin] using
    (volume : Measure (Space n)).toSphere_real_apply_univ

/-- In positive dimension the concrete canonical sphere mass is positive. -/
theorem canonicalSphereArea_pos {n : ℕ} (hn : 0<n) : 0<canonicalSphereArea n := by
  rw [canonicalSphereArea_eq_unitBall]
  have hv : 0<volume.real (ball (0 : Space n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Space n) (by norm_num)).ne'
      measure_ball_lt_top.ne
  exact mul_pos (Nat.cast_pos.mpr hn) hv

/-- The critical planar normalization has the actual value 2*pi. -/
theorem canonicalSphereArea_two : canonicalSphereArea 2 = 2*Real.pi := by
  rw [canonicalSphereArea_eq_unitBall]
  simp only [Space,Measure.real,EuclideanSpace.volume_ball_fin_two,ENNReal.ofReal_one,
    one_pow,one_mul,ENNReal.toReal_ofReal Real.pi_nonneg,Nat.cast_ofNat]

end BMCompactPDE
#print axioms BMCompactPDE.canonicalSphereArea_eq_unitBall
#print axioms BMCompactPDE.canonicalSphereArea_pos
#print axioms BMCompactPDE.canonicalSphereArea_two
