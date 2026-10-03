import NLS.ZakharovShabat.ClassicalSobolevRemainderTimeBounds
import NLS.ZakharovShabat.ClassicalFreeDiscriminant

/-! # Uniform inverse-frequency error for the physical H¹ discriminant -/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The trace error is the sum of the two diagonal solution errors. -/
theorem classicalDiscriminant_sub_free_eq_remainder_trace
    (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant φ z-freeDiscriminant z =
      (classicalSolutionRemainder φ z (1,0) 1).1+
      (classicalSolutionRemainder φ z (0,1) 1).2 := by
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
    Matrix.trace_fin_two_of,classicalSolutionRemainder,classicalFreeVector]
  simp only [Prod.fst_sub,Prod.snd_sub,mul_one,Complex.ofReal_one]
  rw [freeDiscriminant,Complex.two_cos]
  ring_nf

/-- Both diagonal column estimates give a uniform O(1/|z|) trace error on H¹ balls. -/
theorem norm_classicalDiscriminant_sub_free_sobolev_strip_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) :
    ‖classicalDiscriminant (classicalSobolevPotential a) z-freeDiscriminant z‖ ≤
      2*classicalSobolevErrorConstant M H/‖z‖ := by
  have h1 := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH
    (1,0) ⟨1,by constructor <;> norm_num⟩
  have h2 := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH
    (0,1) ⟨1,by constructor <;> norm_num⟩
  rw [classicalDiscriminant_sub_free_eq_remainder_trace]
  apply ((norm_add_le _ _).trans (add_le_add (norm_fst_le _) (norm_snd_le _))).trans
  convert add_le_add h1 h2 using 1
  simp [classicalSobolevErrorConstant]
  ring

end NLS.ZakharovShabat
