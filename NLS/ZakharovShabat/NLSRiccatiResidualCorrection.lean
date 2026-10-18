import NLS.ZakharovShabat.NLSRiccatiLeadingResidual
import NLS.ZakharovShabat.NLSRiccatiResidualDegree

/-! # The Riccati residual after removing its leading density

The correction gains one exact inverse-frequency power and needs only bounds for lower Riccati densities.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Above the leading order, every residual coefficient comes entirely
from the quadratic truncation term, with no differentiated density. -/
theorem coeff_nlsRiccatiResidualPolynomial_above (a b : ℝ → ℂ) (N k : ℕ) (hk : N < k) :
    (nlsRiccatiResidualPolynomial a b N).coeff k =
      -((Polynomial.C a*(nlsRiccatiTruncation a b N*nlsRiccatiTruncation a b N))*Polynomial.X^2).coeff k := by
  cases k with
  | zero => omega
  | succ j =>
    unfold nlsRiccatiResidualPolynomial
    rw [Polynomial.coeff_sub,Polynomial.coeff_sub,Polynomial.coeff_add,
      Polynomial.coeff_mul_X,coeff_nlsRiccatiTruncation,coeff_nlsRiccatiDerivativeTruncation,
      if_neg (by omega),if_neg (by omega)]
    simp

/-- Removing the leading density leaves a correction bounded using only
lower-density suprema; no derivative supremum occurs. -/
theorem norm_nlsRiccatiResidual_correction_le
    (a b : ℝ → ℂ) (N : ℕ) (A U : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : ∀ x : ℝ, ‖a x‖ ≤ A)
    (hρ : ∀ j < N, ∀ x : ℝ, ‖nlsRiccatiDensity a b j x‖ ≤ U)
    (x : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
      nlsRiccatiDensity a b N x*w^N‖ ≤
        (∑ k ∈ Finset.range (2*N+3), A*(k+1)*U^2)*‖w‖^(N+1) := by
  let P := nlsRiccatiTruncation a b N
  let Q := nlsRiccatiResidualPolynomial a b N+Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N
  have hdiv : Polynomial.X^(N+1) ∣ Q := X_pow_succ_dvd_nlsRiccatiResidual_correction a b N
  have hdegree : Q.natDegree < 2*N+3 := by
    have h := Polynomial.natDegree_add_le (nlsRiccatiResidualPolynomial a b N)
      (Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N)
    have h1 := natDegree_nlsRiccatiResidualPolynomial_le a b N
    have h2 : (Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N).natDegree ≤ N :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    dsimp only [Q]
    omega
  have hP (j : ℕ) : ‖P.coeff j x‖ ≤ U := by
    dsimp only [P]
    rw [coeff_nlsRiccatiTruncation]
    split_ifs with hj
    · exact hρ j hj x
    · simpa using hU
  have hprod (j : ℕ) : ‖(P*P).coeff j x‖ ≤ (j+1)*U^2 := by
    rw [Polynomial.coeff_mul]
    simp only [Finset.sum_apply,Pi.mul_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ ij ∈ Finset.antidiagonal j, U^2 := by
        apply Finset.sum_le_sum
        intro ij _
        rw [norm_mul,pow_two]
        exact mul_le_mul (hP ij.1) (hP ij.2) (norm_nonneg _) hU
      _ = _ := by simp
  have hcoeff (k : ℕ) (hk : N < k) : ‖Q.coeff k x‖ ≤ A*(k+1)*U^2 := by
    dsimp only [Q]
    rw [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,if_neg (by omega),add_zero,
      coeff_nlsRiccatiResidualPolynomial_above a b N k hk]
    simp only [Pi.neg_apply,norm_neg]
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs with hk2
    · rw [Polynomial.coeff_C_mul]
      change ‖a x*((P*P).coeff (k-2) x)‖ ≤ _
      rw [norm_mul]
      apply (mul_le_mul (ha x) (hprod (k-2)) (norm_nonneg _) hA).trans
      have hkr : ((k-2:ℕ):ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast (show k-2+1 ≤ k+1 by omega)
      nlinarith [mul_nonneg hA (sq_nonneg U)]
    · simp only [Pi.zero_apply,norm_zero]
      positivity
  have he : Q.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w =
      (nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
        nlsRiccatiDensity a b N x*w^N := by
    simp [Q]
  rw [← he,Polynomial.eval₂_eq_sum_range' _ hdegree]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  change ‖Q.coeff k x*w^k‖ ≤ _
  by_cases hk : k < N+1
  · rw [(Polynomial.X_pow_dvd_iff.mp hdiv) k hk]
    simp only [Pi.zero_apply,zero_mul,norm_zero]
    positivity
  · rw [norm_mul,norm_pow]
    exact mul_le_mul (hcoeff k (by omega))
      (pow_le_pow_of_le_one (norm_nonneg w) hw (by omega)) (by positivity) (by positivity)

end NLS.ZakharovShabat
