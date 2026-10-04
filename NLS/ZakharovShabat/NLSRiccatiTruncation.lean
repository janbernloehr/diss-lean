import NLS.ZakharovShabat.NLSRiccatiHierarchy
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

/-! # Exact cancellation in finite Riccati expansions

The degree-`N-1` truncation of the density series has a Riccati residual
divisible by `X^N`. This is an exact polynomial identity at every order.
-/
noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The first `N` density coefficients as a polynomial in inverse frequency. -/
def nlsRiccatiTruncation (a b : ℝ → ℂ) (N : ℕ) : Polynomial (ℝ → ℂ) :=
  PowerSeries.trunc N (nlsRiccatiSeries a b)

/-- The spatial derivative of every retained coefficient. -/
def nlsRiccatiDerivativeTruncation (a b : ℝ → ℂ) (N : ℕ) : Polynomial (ℝ → ℂ) :=
  PowerSeries.trunc N (nlsRiccatiDerivativeSeries a b)

/-- The residual before evaluating inverse frequency. Its sign is the
negative of the residual in the differential Riccati equation. -/
def nlsRiccatiResidualPolynomial (a b : ℝ → ℂ) (N : ℕ) : Polynomial (ℝ → ℂ) :=
  nlsRiccatiTruncation a b N + Polynomial.C b -
    nlsRiccatiDerivativeTruncation a b N * Polynomial.X -
    (Polynomial.C a * (nlsRiccatiTruncation a b N * nlsRiccatiTruncation a b N)) * Polynomial.X^2

@[simp] theorem coeff_nlsRiccatiTruncation (a b : ℝ → ℂ) (N k : ℕ) :
    (nlsRiccatiTruncation a b N).coeff k = if k < N then nlsRiccatiDensity a b k else 0 := by
  simp [nlsRiccatiTruncation,nlsRiccatiSeries,PowerSeries.coeff_trunc]

@[simp] theorem coeff_nlsRiccatiDerivativeTruncation (a b : ℝ → ℂ) (N k : ℕ) :
    (nlsRiccatiDerivativeTruncation a b N).coeff k = if k < N then deriv (nlsRiccatiDensity a b k) else 0 := by
  simp [nlsRiccatiDerivativeTruncation,nlsRiccatiDerivativeSeries,PowerSeries.coeff_trunc]

/-- Every coefficient below the truncation order cancels exactly. -/
theorem coeff_nlsRiccatiResidualPolynomial_eq_zero (a b : ℝ → ℂ) (N k : ℕ) (hk : k < N) :
    (nlsRiccatiResidualPolynomial a b N).coeff k = 0 := by
  rcases k with _ | _ | k
  · simp [nlsRiccatiResidualPolynomial,hk]
  · simp [nlsRiccatiResidualPolynomial,hk,show 0 < N by omega,
      Polynomial.coeff_mul_X_pow',deriv.neg']
    ext x
    simp
  · unfold nlsRiccatiResidualPolynomial
    rw [Polynomial.coeff_sub,Polynomial.coeff_sub,Polynomial.coeff_add,
      Polynomial.coeff_C,if_neg (by omega)]
    change _ - _ - ((Polynomial.C a * (nlsRiccatiTruncation a b N * nlsRiccatiTruncation a b N)) *
      Polynomial.X^2).coeff (k+2) = 0
    rw [Polynomial.coeff_mul_X_pow,Polynomial.coeff_mul_X,Polynomial.coeff_C_mul,Polynomial.coeff_mul]
    simp only [coeff_nlsRiccatiTruncation,coeff_nlsRiccatiDerivativeTruncation,
      if_pos hk,if_pos (show k+1 < N by omega),add_zero]
    have hs : (∑ ij ∈ Finset.antidiagonal k,
        (if ij.1 < N then nlsRiccatiDensity a b ij.1 else 0) *
        (if ij.2 < N then nlsRiccatiDensity a b ij.2 else 0)) =
        ∑ ij ∈ Finset.antidiagonal k, nlsRiccatiDensity a b ij.1 * nlsRiccatiDensity a b ij.2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      rw [if_pos (by omega),if_pos (by omega)]
    rw [hs,nlsRiccatiDensity_succ_succ]
    abel

/-- Exact order-`N` divisibility, without regularity hypotheses. -/
theorem X_pow_dvd_nlsRiccatiResidualPolynomial (a b : ℝ → ℂ) (N : ℕ) :
    Polynomial.X^N ∣ nlsRiccatiResidualPolynomial a b N :=
  Polynomial.X_pow_dvd_iff.mpr (fun k hk => coeff_nlsRiccatiResidualPolynomial_eq_zero a b N k hk)

end NLS.ZakharovShabat
