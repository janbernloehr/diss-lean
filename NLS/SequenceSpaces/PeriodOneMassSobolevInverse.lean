import NLS.SequenceSpaces.PeriodOneMassResolvent
import NLS.SequenceSpaces.SobolevDerivative

/-! The ACTUAL massive period-one resolvent gains one full Sobolev
order, with its original symbol and a bound uniform in the mass.
The L2-to-H1 version retains every original raw coefficient. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

theorem periodOneMassInverse_sobolev_bound (s : ℝ) (m : ℕ) (k : ℤ) :
    Weight.sobolev (s + 1) k * ‖(periodOneMassSymbol m k)⁻¹‖ ≤ 2 * Weight.sobolev s k := by
  have h := mul_le_mul_of_nonneg_left (norm_periodOneMassSymbol_inv_le_bracket m k)
    ((Weight.sobolev s).positive k).le
  rw [Weight.sobolev_add, Weight.sobolev_apply (s := 1), Real.rpow_one]
  have hb : 1 + |(k : ℝ)| ≠ 0 := ne_of_gt (by positivity)
  have he : Weight.sobolev s k * (2 / (1 + |(k : ℝ)|)) * (1 + |(k : ℝ)|) =
      2 * Weight.sobolev s k := by field_simp
  have ht := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1 + |(k : ℝ)|)
  rw [he] at ht
  nlinarith

def periodOneMassSobolevInverse (s : ℝ) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] WeightedCoeff (Weight.sobolev (s + 1)) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun k => (periodOneMassSymbol m k)⁻¹)
    2 (by norm_num) (periodOneMassInverse_sobolev_bound s m)

theorem periodOneMassSobolevInverse_apply (s : ℝ) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.sobolev s) p) (k : ℤ) :
    (periodOneMassSobolevInverse s m p a).val k = (periodOneMassSymbol m k)⁻¹ * a.val k := rfl

def periodOneMassL2ToH1 (m : ℕ) : Coeff 2 →L[ℂ] ZakharovShabat.ScalarDomain 2 :=
  (WeightedCoeff.weightedMultiplierCLM Weight.one (Weight.sobolev 1)
    (fun k => (periodOneMassSymbol m k)⁻¹) 2 (by norm_num) (by
      intro k
      simpa only [zero_add, Weight.sobolev_apply, Real.rpow_zero, Real.rpow_one, Weight.one_apply]
        using periodOneMassInverse_sobolev_bound 0 m k)).comp
    (WeightedCoeff.weightIsometry Weight.one 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem periodOneMassL2ToH1_apply (m : ℕ) (a : Coeff 2) (k : ℤ) :
    (periodOneMassL2ToH1 m a).val k = (periodOneMassSymbol m k)⁻¹ * a k := by
  change (periodOneMassSymbol m k)⁻¹ * (a k / (Weight.one k : ℂ)) = _
  simp only [Weight.one_apply, ofReal_one, div_one]

end NLS
