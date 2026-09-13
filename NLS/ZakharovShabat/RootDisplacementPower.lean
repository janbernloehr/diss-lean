import NLS.ZakharovShabat.ResonantDeterminantAnalytic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Root displacement powers without choosing a square-root branch

The determinant equation gives a squared residual equal to the product of
the two off-diagonal coefficients. Arithmetic-geometric and power-mean
inequalities give the displacement estimate directly. Expanding the full
coefficients retains their leading Fourier modes; these terms cannot be
absorbed into an extra small potential-norm factor.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- A quadratic determinant zero has residual at most the arithmetic mean of the off-diagonal moduli. -/
theorem norm_quadraticRoot_residual_le (q a b c : ℂ) (hz : (q-a)^2-b*c = 0) :
    ‖q-a‖ ≤ (‖b‖+‖c‖)/2 := by
  have he := congrArg norm (sub_eq_zero.mp hz)
  simp only [norm_pow, norm_mul] at he
  nlinarith [norm_nonneg (q-a), norm_nonneg b, norm_nonneg c, sq_nonneg (‖b‖-‖c‖)]

/-- Each determinant root obeys the full-coefficient power estimate for every real exponent at least one. -/
theorem norm_quadraticRoot_rpow_le {P : ℝ} (hP : 1 ≤ P) (q a b c : ℂ)
    (hz : (q-a)^2-b*c = 0) :
    ‖q‖^P ≤ (2 : ℝ)^(P-1) * (‖a‖^P + (‖b‖^P+‖c‖^P)/2) := by
  have hres := norm_quadraticRoot_residual_le q a b c hz
  have hmean : ((1/2 : ℝ)*‖b‖+(1/2 : ℝ)*‖c‖)^P ≤ (1/2 : ℝ)*‖b‖^P+(1/2 : ℝ)*‖c‖^P := by
    exact_mod_cast NNReal.rpow_arith_mean_le_arith_mean2_rpow (1/2) (1/2)
      (⟨‖b‖,norm_nonneg _⟩ : ℝ≥0) (⟨‖c‖,norm_nonneg _⟩ : ℝ≥0) (by norm_num) hP
  have hresP : ‖q-a‖^P ≤ (‖b‖^P+‖c‖^P)/2 := by
    calc
      _ ≤ ((1/2 : ℝ)*‖b‖+(1/2 : ℝ)*‖c‖)^P :=
        Real.rpow_le_rpow (norm_nonneg _) (by linarith) (zero_le_one.trans hP)
      _ ≤ _ := by linarith
  have hadd : (‖a‖+‖q-a‖)^P ≤ (2 : ℝ)^(P-1)*(‖a‖^P+‖q-a‖^P) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨‖a‖,norm_nonneg _⟩ : ℝ≥0) (⟨‖q-a‖,norm_nonneg _⟩ : ℝ≥0) hP
  calc
    _ ≤ (‖a‖+‖q-a‖)^P := Real.rpow_le_rpow (norm_nonneg _)
      (by simpa only [add_comm] using norm_le_norm_sub_add q a) (zero_le_one.trans hP)
    _ ≤ _ := hadd.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hresP) (by positivity))

/-- Separating a leading coefficient from its remainder keeps both power terms. -/
theorem norm_coefficient_rpow_le {P : ℝ} (hP : 1 ≤ P) (b l : ℂ) :
    ‖b‖^P ≤ (2 : ℝ)^(P-1)*(‖l‖^P+‖b-l‖^P) := by
  have hmean : (‖l‖+‖b-l‖)^P ≤ (2 : ℝ)^(P-1)*(‖l‖^P+‖b-l‖^P) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨‖l‖,norm_nonneg _⟩ : ℝ≥0) (⟨‖b-l‖,norm_nonneg _⟩ : ℝ≥0) hP
  exact (Real.rpow_le_rpow (norm_nonneg _)
    (by simpa only [add_comm] using norm_le_norm_sub_add b l) (zero_le_one.trans hP)).trans hmean

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual determinant root estimate, retaining both signed leading Fourier coefficients. -/
theorem resonantRoot_displacement_rpow_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ)
    (hz : resonantDeterminantExtension hp w φ n z = 0) :
    ‖z-(Real.pi : ℂ)*n‖^p.toReal ≤
      (2 : ℝ)^(p.toReal-1) * (‖weightedResonantAExtension hp w φ n z‖^p.toReal +
        (2 : ℝ)^(p.toReal-1) / 2 *
          (‖φ.snd.val (2*n)‖^p.toReal + ‖φ.fst.val (-(2*n))‖^p.toReal +
            ‖weightedResonantBPlusExtension hp w φ n z-φ.snd.val (2*n)‖^p.toReal +
            ‖weightedResonantBMinusExtension hp w φ n z-φ.fst.val (-(2*n))‖^p.toReal)) := by
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  have hroot := norm_quadraticRoot_rpow_le hP (z-(Real.pi : ℂ)*n)
    (weightedResonantAExtension hp w φ n z) (weightedResonantBPlusExtension hp w φ n z)
    (weightedResonantBMinusExtension hp w φ n z) hz
  have hplus := norm_coefficient_rpow_le hP (weightedResonantBPlusExtension hp w φ n z) (φ.snd.val (2*n))
  have hminus := norm_coefficient_rpow_le hP (weightedResonantBMinusExtension hp w φ n z) (φ.fst.val (-(2*n)))
  apply hroot.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  nlinarith

end NLS.ZakharovShabat
