import NLS.SequenceSpaces.RealMeanZeroHalfFourierEquiv

/-! Exact signed and squared normalization of the original free inverse
half-Fourier multiplier. -/
noncomputable section
namespace NLS.WeightedCoeff

theorem halfFourierInverseSymbol_positive_sq (n : ℕ+) :
    halfFourierInverseSymbol (n:ℤ)^2=((2*Real.pi*(n:ℕ):ℝ):ℂ) := by
  have hn : (1:ℝ)≤(n:ℕ) := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  change ((Real.sqrt (2*Real.pi)*Real.sqrt (max 1 |((n:ℕ):ℝ)|):ℝ):ℂ)^2=_
  rw [abs_of_nonneg (by positivity : (0:ℝ)≤(n:ℕ)),max_eq_right hn,← Complex.ofReal_pow,mul_pow,
    Real.sq_sqrt (by positivity : 0≤2*Real.pi),Real.sq_sqrt (by positivity : (0:ℝ)≤(n:ℕ))]

end NLS.WeightedCoeff
