import NLS.SequenceSpaces.Weighted

/-!
# Weights compatible with tempered distributions

A polynomial upper bound on the reciprocal weight ensures weighted Banach
coefficients grow at most polynomially. Every real Sobolev weight satisfies
this condition, including negative and fractional regularities.
-/

noncomputable section
namespace NLS.Weight

/-- The reciprocal weight grows at most polynomially along the Fourier lattice. -/
def HasTemperedInverse (w : Weight) : Prop :=
  ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, 1 / w n ≤ C * (1 + |(n : ℝ)|) ^ K

theorem hasTemperedInverse_one : HasTemperedInverse one := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro n
  simp

/-- All real Sobolev regularities give polynomially bounded reciprocal weights. -/
theorem hasTemperedInverse_sobolev (s : ℝ) : HasTemperedInverse (sobolev s) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (-s)
  refine ⟨K, 1, by norm_num, fun n => ?_⟩
  simp only [sobolev_apply, one_mul]
  have hb : 1 ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
  calc
    _ = (1 + |(n : ℝ)|) ^ (-s) := by rw [Real.rpow_neg (by positivity), one_div]
    _ ≤ (1 + |(n : ℝ)|) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hK
    _ = _ := Real.rpow_natCast _ _

end NLS.Weight
