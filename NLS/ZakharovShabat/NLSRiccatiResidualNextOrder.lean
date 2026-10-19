import NLS.ZakharovShabat.NLSRiccatiResidualCorrection

/-! # The next coefficient in the Riccati residual

Isolating the next residual coefficient improves the truncation error by another inverse-frequency power using only lower undifferentiated densities.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The next coefficient after the leading Riccati density in the actual
truncation residual. It involves only lower, undifferentiated densities. -/
def nlsRiccatiResidualNextDensity (a b : ℝ → ℂ) (N : ℕ) : ℝ → ℂ :=
  (nlsRiccatiResidualPolynomial a b N).coeff (N+1)

/-- Every coefficient above the leading order is bounded using only the
potential and lower-density suprema. -/
theorem norm_coeff_nlsRiccatiResidualPolynomial_above_le
    (a b : ℝ → ℂ) (N k : ℕ) (hk : N < k) (A U : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : ∀ x : ℝ, ‖a x‖ ≤ A)
    (hρ : ∀ j < N, ∀ x : ℝ, ‖nlsRiccatiDensity a b j x‖ ≤ U) (x : ℝ) :
    ‖(nlsRiccatiResidualPolynomial a b N).coeff k x‖ ≤ A*(k+1)*U^2 := by
  let P := nlsRiccatiTruncation a b N
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
  rw [coeff_nlsRiccatiResidualPolynomial_above a b N k hk]
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

/-- Removing the next explicit residual coefficient gains a second
inverse-frequency power using no additional derivative bound. -/
theorem norm_nlsRiccatiResidual_next_order_le
    (a b : ℝ → ℂ) (N : ℕ) (A U : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : ∀ x : ℝ, ‖a x‖ ≤ A)
    (hρ : ∀ j < N, ∀ x : ℝ, ‖nlsRiccatiDensity a b j x‖ ≤ U)
    (x : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
      nlsRiccatiDensity a b N x*w^N-nlsRiccatiResidualNextDensity a b N x*w^(N+1)‖ ≤
        (∑ k ∈ Finset.range (2*N+3), A*(k+1)*U^2)*‖w‖^(N+2) := by
  let Q := nlsRiccatiResidualPolynomial a b N+Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N
  let T := Q-Polynomial.C (nlsRiccatiResidualNextDensity a b N)*Polynomial.X^(N+1)
  have hQ : Polynomial.X^(N+1) ∣ Q := X_pow_succ_dvd_nlsRiccatiResidual_correction a b N
  have hdiv : Polynomial.X^(N+2) ∣ T := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    dsimp only [T]
    rw [Polynomial.coeff_sub,Polynomial.coeff_C_mul_X_pow]
    by_cases he : k = N+1
    · subst k
      simp [Q,nlsRiccatiResidualNextDensity]
    · rw [if_neg he,sub_zero]
      exact (Polynomial.X_pow_dvd_iff.mp hQ) k (by omega)
  have hdegree : T.natDegree < 2*N+3 := by
    have h := Polynomial.natDegree_sub_le Q
      (Polynomial.C (nlsRiccatiResidualNextDensity a b N)*Polynomial.X^(N+1))
    have hq := Polynomial.natDegree_add_le (nlsRiccatiResidualPolynomial a b N)
      (Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N)
    have h1 := natDegree_nlsRiccatiResidualPolynomial_le a b N
    have h2 : (Polynomial.C (nlsRiccatiDensity a b N)*Polynomial.X^N).natDegree ≤ N :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    have h3 : (Polynomial.C (nlsRiccatiResidualNextDensity a b N)*Polynomial.X^(N+1)).natDegree ≤ N+1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    dsimp only [T,Q] at *
    omega
  have hcoeff (k : ℕ) (hk : N+2 ≤ k) : ‖T.coeff k x‖ ≤ A*(k+1)*U^2 := by
    dsimp only [T,Q]
    rw [Polynomial.coeff_sub,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow,if_neg (by omega),if_neg (by omega),add_zero,sub_zero]
    exact norm_coeff_nlsRiccatiResidualPolynomial_above_le a b N k (by omega) A U hA hU ha hρ x
  have he : T.eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w =
      (nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
      nlsRiccatiDensity a b N x*w^N-nlsRiccatiResidualNextDensity a b N x*w^(N+1) := by
    simp [T,Q]
  rw [← he,Polynomial.eval₂_eq_sum_range' _ hdegree]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  change ‖T.coeff k x*w^k‖ ≤ _
  by_cases hk : k < N+2
  · rw [(Polynomial.X_pow_dvd_iff.mp hdiv) k hk]
    simp only [Pi.zero_apply,zero_mul,norm_zero]
    positivity
  · rw [norm_mul,norm_pow]
    exact mul_le_mul (hcoeff k (by omega))
      (pow_le_pow_of_le_one (norm_nonneg w) hw (by omega)) (by positivity) (by positivity)

end NLS.ZakharovShabat
