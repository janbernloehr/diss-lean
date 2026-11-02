import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.SequenceSpaces.SobolevEmbedding
import NLS.SequenceSpaces.SandwichMajorant

/-! # Weighted realization of an indexed sequence plus a bounded error

Multiplication of an ℓr sequence by its index loses one derivative.
A uniformly bounded error also belongs to the weight-minus-one target
for every finite r > 1. The raw coordinate at zero is retained.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

/-- The reciprocal bracket is in every sequence exponent above one. -/
def inverseBracketCoeffs (r : ℝ≥0∞) (hr1 : 1 < r) : Coeff r :=
  ⟨fun n => (Weight.sobolev 1 n:ℂ)⁻¹,Weight.inverse_sobolev_one_memlp hr1⟩

@[simp] theorem inverseBracketCoeffs_apply (r : ℝ≥0∞) (hr1 : 1 < r) (n : ℤ) :
    inverseBracketCoeffs r hr1 n = (Weight.sobolev (-1) n:ℂ) := by
  simp only [inverseBracketCoeffs,Weight.sobolev_apply,Real.rpow_one,Real.rpow_neg_one,Complex.ofReal_inv]

/-- The index times the reciprocal bracket has norm at most one. -/
theorem norm_inverseBracket_mul_index_le_one (n : ℤ) :
    ‖(Weight.sobolev (-1) n:ℂ)*(n:ℂ)‖ ≤ 1 := by
  simp only [norm_mul,Complex.norm_intCast,Complex.norm_real,Weight.sobolev_apply,
    Real.rpow_neg_one,Real.norm_of_nonneg (by positivity : 0 ≤ (1+|(n:ℝ)|)⁻¹)]
  rw [mul_comm,← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr (by linarith)

/-- An index multiple of an actual ℓr sequence plus a bounded error has
an actual weighted realization, with quantitative norm control. -/
theorem exists_negOne_weighted_of_bounded_error
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r)
    (f : ℤ → ℂ) (b : Coeff r) (c : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n : ℤ, ‖f n-c*(n:ℂ)*b n‖ ≤ C) :
    ∃ a : WeightedCoeff (Weight.sobolev (-1)) r,
      (∀ n, a.val n = f n) ∧ ‖a‖ ≤ ‖c‖*‖b‖+C*‖inverseBracketCoeffs r hr1‖ := by
  let d := inverseBracketCoeffs r hr1
  let B := (‖c‖:ℂ) • magnitude b+(C:ℂ) • magnitude d
  have hB (n : ℤ) : ‖B n‖ = ‖c‖*‖b n‖+C*‖d n‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,magnitude_apply,
      ← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hpoint (n : ℤ) : ‖(Weight.sobolev (-1) n:ℂ)*f n‖ ≤ ‖B n‖ := by
    have he : (Weight.sobolev (-1) n:ℂ)*f n =
        ((Weight.sobolev (-1) n:ℂ)*(n:ℂ))*c*b n+
          (Weight.sobolev (-1) n:ℂ)*(f n-c*(n:ℂ)*b n) := by ring
    rw [he,hB]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    apply add_le_add
    · calc
        _ ≤ 1*‖c‖*‖b n‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by simpa only [norm_mul] using norm_inverseBracket_mul_index_le_one n)
            (norm_nonneg c)) (norm_nonneg _)
        _ = _ := by ring
    · simpa only [d,inverseBracketCoeffs_apply,mul_comm] using
        mul_le_mul_of_nonneg_left (hf n) (norm_nonneg (Weight.sobolev (-1) n:ℂ))
  let a : WeightedCoeff (Weight.sobolev (-1)) r := ⟨f,(lp.memℓp B).mono' hpoint⟩
  refine ⟨a,fun _ => rfl,?_⟩
  have ha : ‖a‖ ≤ ‖B‖ := by
    change ‖WeightedCoeff.weightEquiv (Weight.sobolev (-1)) r a‖ ≤ ‖B‖
    exact lp.norm_mono (x := WeightedCoeff.weightEquiv (Weight.sobolev (-1)) r a)
      (y := B) (zero_lt_one.trans hr1).ne' hpoint
  apply ha.trans
  apply (norm_add_le _ _).trans_eq
  simp only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg c),Real.norm_of_nonneg hC,
    norm_magnitude]
  rfl

end NLS.Coeff
