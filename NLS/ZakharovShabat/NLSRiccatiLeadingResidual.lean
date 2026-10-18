import NLS.ZakharovShabat.NLSRiccatiTruncation

/-! # The leading Riccati residual

The coefficient at the first possible nonzero order is exactly the negative next Riccati density. Removing it improves polynomial divisibility by one order.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The coefficient at the first possible nonzero order is the negative next Riccati density,
including order zero. This separates the top Sobolev derivative. -/
theorem coeff_nlsRiccatiResidualPolynomial_leading (a b : ℝ → ℂ) (N : ℕ) :
    (nlsRiccatiResidualPolynomial a b N).coeff N = -nlsRiccatiDensity a b N := by
  rcases N with _ | _ | n
  · simp [nlsRiccatiResidualPolynomial,nlsRiccatiTruncation,nlsRiccatiDerivativeTruncation]
  · simp [nlsRiccatiResidualPolynomial,Polynomial.coeff_mul_X_pow',deriv.neg']
    ext x
    simp
  · unfold nlsRiccatiResidualPolynomial
    rw [Polynomial.coeff_sub,Polynomial.coeff_sub,Polynomial.coeff_add,
      Polynomial.coeff_C,if_neg (by omega)]
    change _ - _ - ((Polynomial.C a * (nlsRiccatiTruncation a b (n+2) * nlsRiccatiTruncation a b (n+2))) *
      Polynomial.X^2).coeff (n+2) = _
    rw [Polynomial.coeff_mul_X_pow,Polynomial.coeff_mul_X,Polynomial.coeff_C_mul,Polynomial.coeff_mul]
    simp only [coeff_nlsRiccatiTruncation,coeff_nlsRiccatiDerivativeTruncation,
      if_neg (show ¬n+2 < n+2 by omega),if_pos (show n+1 < n+2 by omega),add_zero,zero_sub]
    have hs : (∑ ij ∈ Finset.antidiagonal n,
        (if ij.1 < n+2 then nlsRiccatiDensity a b ij.1 else 0) *
        (if ij.2 < n+2 then nlsRiccatiDensity a b ij.2 else 0)) =
        ∑ ij ∈ Finset.antidiagonal n, nlsRiccatiDensity a b ij.1 * nlsRiccatiDensity a b ij.2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      rw [if_pos (by omega),if_pos (by omega)]
    rw [hs,nlsRiccatiDensity_succ_succ]
    abel

/-- Subtracting the top derivative term improves exact residual divisibility by one order. -/
theorem X_pow_succ_dvd_nlsRiccatiResidual_correction (a b : ℝ → ℂ) (N : ℕ) :
    Polynomial.X^(N+1) ∣ nlsRiccatiResidualPolynomial a b N+
      Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  rw [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow]
  by_cases h : k=N
  · subst k
    simp [coeff_nlsRiccatiResidualPolynomial_leading]
  · rw [coeff_nlsRiccatiResidualPolynomial_eq_zero a b N k (by omega)]
    simp [h]

end NLS.ZakharovShabat
