import NLS.SequenceSpaces.MixedYoung
import NLS.SequenceSpaces.SobolevEmbedding

/-!
# Why B.3 requires positive auxiliary exponents

The printed formula divides by the auxiliary exponents. Its zero endpoints
are undefined, even though the printed ordering permits them. The conditions
below only diagnose a transcription using Lean's totalized division.

Actual nonzero input sequences show divergence of the inner sum at alpha zero
and of the middle sum at beta zero. In the latter case every inner sum exists
and is strictly positive. Thus neither example relies on a `0^0` convention.
These results do not refute the well-defined positive-exponent inequality.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- A syntactic transcription of B.3's nonnegative conditions using Lean's totalized
real division. At zero this is not a definition of the mathematical source formula. -/
structure TotalizedMixedYoungConditions (α β γ p₁ p₂ p₃ : ℝ) : Prop where
  alpha_nonneg : 0 ≤ α
  beta_nonneg : 0 ≤ β
  beta_le_p₁ : β ≤ p₁
  p₁_le_gamma : p₁ ≤ γ
  alpha_le_p₂ : α ≤ p₂
  alpha_le_p₃ : α ≤ p₃
  relation : 1 / α + 1 / β + 1 / γ = 1 / p₁ + 1 / p₂ + 1 / p₃

/-- Totalizing division admits a zero inner exponent despite positive input exponents. -/
theorem printedMixedYoung_zero_inner : TotalizedMixedYoungConditions 0 1 1 1 2 2 := by
  constructor <;> norm_num

/-- Totalizing division also admits a zero middle exponent. -/
theorem printedMixedYoung_zero_middle : TotalizedMixedYoungConditions 1 0 1 1 2 2 := by
  constructor <;> norm_num

end NLS

namespace NLS.Coeff

/-- The everywhere nonzero square-summable sequence `(1 + |n|)⁻¹`. -/
def b3PositiveInput : Coeff 2 :=
  ⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹, Weight.inverse_sobolev_one_memlp (by norm_num)⟩

/-- Every coefficient is nonzero, so zero powers need no `0^0` convention. -/
theorem b3PositiveInput_ne_zero (n : ℤ) : b3PositiveInput n ≠ 0 := by
  change (Weight.sobolev 1 n : ℂ)⁻¹ ≠ 0
  apply inv_ne_zero
  rw [Weight.sobolev_apply, Real.rpow_one]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- All inner products at zero output and middle frequency are nonzero. -/
theorem b3_zero_inner_terms_nonzero (m : ℤ) :
    (lp.single 1 0 (1 : ℂ) : Coeff 1) (0 - 0) * b3PositiveInput (0 - m) * b3PositiveInput m ≠ 0 := by
  simpa [lp.single_apply, Pi.single_apply] using
    mul_ne_zero (b3PositiveInput_ne_zero (0 - m)) (b3PositiveInput_ne_zero m)

/-- At zero inner exponent the row consists of ones and does not converge. -/
theorem b3_zero_inner_not_summable :
    ¬Summable (fun m : ℤ => ‖(lp.single 1 0 (1 : ℂ) : Coeff 1) (0 - 0) *
      b3PositiveInput (0 - m) * b3PositiveInput m‖ ^ (0 : ℝ)) := by
  simpa only [Real.rpow_zero, summable_const_iff] using (one_ne_zero : (1 : ℝ) ≠ 0)


/-- The everywhere nonzero summable sequence `(1 + |n|)⁻²`. -/
def b3PositiveOneInput : Coeff 1 := by
  refine ⟨fun n => ((‖b3PositiveInput n‖ ^ 2 : ℝ) : ℂ), ?_⟩
  apply memℓp_gen
  simpa only [ENNReal.toReal_one, Real.rpow_one, Complex.norm_real, Real.norm_eq_abs,
    abs_pow, abs_norm, ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp b3PositiveInput).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The summable first input has no zero coefficient. -/
theorem b3PositiveOneInput_ne_zero (n : ℤ) : b3PositiveOneInput n ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (b3PositiveInput_ne_zero n)))

/-- With inner exponent one, every inner row is absolutely summable. -/
theorem b3_zero_middle_inner_summable (k l : ℤ) :
    Summable (fun m : ℤ => ‖b3PositiveOneInput (k - l) * b3PositiveInput (l - m) * b3PositiveInput m‖ ^ (1 : ℝ)) := by
  have h : YoungRelation 2 2 ⊤ := by
    simpa [YoungRelation] using (ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2).symm
  have hs := (summable_norm_youngConvolution_terms h b3PositiveInput b3PositiveInput l).mul_left
    ‖b3PositiveOneInput (k - l)‖
  simpa only [norm_mul, Real.rpow_one, mul_assoc] using hs

/-- Every inner row has strictly positive sum, avoiding `0^0` at the middle level. -/
theorem b3_zero_middle_inner_pos (k l : ℤ) :
    0 < ∑' m : ℤ, ‖b3PositiveOneInput (k - l) * b3PositiveInput (l - m) * b3PositiveInput m‖ ^ (1 : ℝ) := by
  have hterm : 0 < ‖b3PositiveOneInput (k - l) * b3PositiveInput (l - 0) * b3PositiveInput 0‖ ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (b3PositiveOneInput_ne_zero _)
      (b3PositiveInput_ne_zero _)) (b3PositiveInput_ne_zero _))
  exact hterm.trans_le ((b3_zero_middle_inner_summable k l).le_tsum 0 (fun _ _ => by positivity))

/-- At zero middle exponent the middle row consists of ones and does not converge. -/
theorem b3_zero_middle_not_summable (k : ℤ) :
    ¬Summable (fun l : ℤ => (∑' m : ℤ,
      ‖b3PositiveOneInput (k - l) * b3PositiveInput (l - m) * b3PositiveInput m‖ ^ (1 : ℝ)) ^ ((0 : ℝ) / 1)) := by
  simpa only [zero_div, Real.rpow_zero, summable_const_iff] using (one_ne_zero : (1 : ℝ) ≠ 0)

end NLS.Coeff
