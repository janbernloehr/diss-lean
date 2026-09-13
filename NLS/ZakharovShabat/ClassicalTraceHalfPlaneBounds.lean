import NLS.ZakharovShabat.ClassicalHalfPlaneBounds
import NLS.ZakharovShabat.ClassicalFreeDiscriminant

/-!
# Quantitative half-plane bounds for the monodromy trace

The normalized trace differs from the normalized free trace by at most
`2 M²/a + 2 M²/a²`, where `M` is the potential supremum norm and `a` is
twice the imaginary height. Both signs and all real spectral parts are covered.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem classicalWeightedSolution_trace (φ : Curve (ℂ × ℂ)) (z c : ℂ) :
    exp c * classicalDiscriminant φ z =
      (classicalWeightedSolution φ z c (1,0) 1).1 +
      (classicalWeightedSolution φ z c (0,1) 1).2 := by
  simp only [classicalWeightedSolution, classicalDiscriminant, classicalMonodromy,
    classicalFundamentalMatrix, Matrix.trace_fin_two_of, Complex.ofReal_one,
    mul_one, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem norm_classicalDiscriminant_upper_sub_free_le (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : 0 < z.im) (hlarge : ‖φ‖^2 ≤ z.im) :
    ‖exp (I*z) * classicalDiscriminant φ z - (1 + exp (2*I*z))‖ ≤
      2*‖φ‖^2/(2*z.im) + 2*‖φ‖^2/(2*z.im)^2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h₁ := (classicalWeightedSolution_upper_bounds φ z hz hlarge (1,0) t).2.1
  have h₂ := (classicalWeightedSolution_upper_bounds φ z hz hlarge (0,1) t).2.2
  have he : exp (I*z) * classicalDiscriminant φ z - (1 + exp (2*I*z)) =
      ((classicalWeightedSolution φ z (I*z) (1,0) 1).1 - 1) +
      ((classicalWeightedSolution φ z (I*z) (0,1) 1).2 - exp (2*I*z)) := by
    rw [classicalWeightedSolution_trace]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  convert! add_le_add h₁ h₂ using 1 <;>
    simp only [t, norm_zero, norm_one, mul_zero, zero_div, add_zero, zero_add,
      mul_one, Complex.ofReal_one]
  ring

theorem norm_classicalDiscriminant_lower_sub_free_le (φ : Curve (ℂ × ℂ))
    (z : ℂ) (hz : z.im < 0) (hlarge : ‖φ‖^2 ≤ -z.im) :
    ‖exp (-I*z) * classicalDiscriminant φ z - (1 + exp (-2*I*z))‖ ≤
      2*‖φ‖^2/(-2*z.im) + 2*‖φ‖^2/(-2*z.im)^2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h₁ := (classicalWeightedSolution_lower_bounds φ z hz hlarge (1,0) t).2.2
  have h₂ := (classicalWeightedSolution_lower_bounds φ z hz hlarge (0,1) t).2.1
  have he : exp (-I*z) * classicalDiscriminant φ z - (1 + exp (-2*I*z)) =
      ((classicalWeightedSolution φ z (-I*z) (1,0) 1).1 - exp (-2*I*z)) +
      ((classicalWeightedSolution φ z (-I*z) (0,1) 1).2 - 1) := by
    rw [classicalWeightedSolution_trace]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  convert! add_le_add h₁ h₂ using 1 <;>
    simp only [t, norm_zero, norm_one, mul_zero, zero_div, add_zero, zero_add,
      mul_one, Complex.ofReal_one]
  ring

end NLS.ZakharovShabat
