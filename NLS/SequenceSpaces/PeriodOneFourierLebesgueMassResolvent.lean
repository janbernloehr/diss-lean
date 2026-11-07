import NLS.SequenceSpaces.PeriodOneMassResolvent
import NLS.SequenceSpaces.WeightedMultiplier

/-! # The exact mass resolvent in every native Fourier-Lebesgue norm

The unit-period mass symbol gains one derivative with a bound independent
of the Banach exponent. All raw Fourier coefficients are preserved.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem periodOneMassSymbol_weighted_inverse_bound (m : ℕ) (s : ℝ) (n : ℤ) :
    Weight.sobolev (s+1) n*‖(periodOneMassSymbol m n)⁻¹‖ ≤ 2*Weight.sobolev s n := by
  have h := norm_periodOneMassSymbol_inv_le_bracket m n
  rw [Weight.sobolev_add]
  change Weight.sobolev s n*((1+|(n : ℝ)|)^((1 : ℝ)))*‖(periodOneMassSymbol m n)⁻¹‖ ≤ _
  rw [Real.rpow_one]
  have hb : 0<1+|(n : ℝ)| := by positivity
  have hw := Weight.positive (Weight.sobolev s) n
  calc
    _ ≤ Weight.sobolev s n*(1+|(n : ℝ)|)*(2/(1+|(n : ℝ)|)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-- The actual mass inverse in FL^(s,p) to FL^(s+1,p), for any Banach exponent. -/
def periodOneFourierLebesgueMassInverse (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev (s+1)) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun n => (periodOneMassSymbol m n)⁻¹)
    2 (by norm_num) (periodOneMassSymbol_weighted_inverse_bound m s)

@[simp]theorem periodOneFourierLebesgueMassInverse_apply
    (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (periodOneFourierLebesgueMassInverse m s p a).val n=
      (periodOneMassSymbol m n)⁻¹*a.val n := rfl

theorem norm_periodOneFourierLebesgueMassInverse_le
    (m : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev s) p) :
    ‖periodOneFourierLebesgueMassInverse m s p a‖ ≤ 2*‖a‖ :=
  WeightedCoeff.norm_weightedMultiplier_le _ _ _ 2 (by norm_num)
    (periodOneMassSymbol_weighted_inverse_bound m s) a

end NLS
