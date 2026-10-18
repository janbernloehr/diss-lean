import NLS.ZakharovShabat.NLSRiccatiTruncation

/-! # A uniform degree bound for the Riccati residual

The support of each residual polynomial has a bound depending only on its truncation order.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- A source-independent support bound for every finite Riccati residual. -/
theorem natDegree_nlsRiccatiResidualPolynomial_le (a b : ℝ → ℂ) (N : ℕ) :
    (nlsRiccatiResidualPolynomial a b N).natDegree ≤ 2*N+2 := by
  have htrunc (P : PowerSeries (ℝ → ℂ)) : (PowerSeries.trunc N P).natDegree ≤ N := by
    rcases N with _ | n
    · simp
    · exact (PowerSeries.natDegree_trunc_lt P n).le
  have hR := htrunc (nlsRiccatiSeries a b)
  have hD := htrunc (nlsRiccatiDerivativeSeries a b)
  change (nlsRiccatiTruncation a b N).natDegree ≤ N at hR
  change (nlsRiccatiDerivativeTruncation a b N).natDegree ≤ N at hD
  unfold nlsRiccatiResidualPolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le (by omega)
      simp
    · have h := (Polynomial.natDegree_mul_le (p := nlsRiccatiDerivativeTruncation a b N)
        (q := Polynomial.X)).trans (Nat.add_le_add hD Polynomial.natDegree_X_le)
      omega
  · have hprod := (Polynomial.natDegree_C_mul_le a
      (nlsRiccatiTruncation a b N*nlsRiccatiTruncation a b N)).trans
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hR hR))
    have hpow : (Polynomial.X^2 : Polynomial (ℝ → ℂ)).natDegree ≤ 2 := by simp
    have h := Polynomial.natDegree_mul_le.trans (Nat.add_le_add hprod hpow)
    omega

end NLS.ZakharovShabat
