import NLS.KdV.HillHamiltonianAbsorption
import NLS.ZakharovShabat.SobolevRealJets
import NLS.ZakharovShabat.SobolevHighestJetEnergy

/-! # Physical all-order Sobolev Hamiltonian norm and coercive bounds with polynomial L2 error. -/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory NLS.Fourier NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillSobolevKinetic_real (m : ℕ) (a : ScalarSobolev m)
    (ha : ∀ n, a.val (-n) = conj (a.val n)) :
    sobolevOddKinetic m (a,a) = (‖hierarchySobolevJetL2 m m le_rfl a‖^2 : ℝ) := by
  unfold sobolevOddKinetic
  have hJ := hierarchySobolevJetL2_real m m le_rfl a a
    (fun n => by simpa only [neg_neg] using ha (-n))
  nth_rw 2 [hJ]
  let A := Coeff.reflection (hierarchySobolevJetL2 m m le_rfl a)
  have he : Coeff.dualPairing A (star A) = inner ℂ A A := by
    rw [Coeff.dualPairing_apply, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    rw [RCLike.inner_apply', lp.star_apply, mul_comm]
    rfl
  change Coeff.dualPairing A (star A) = _
  rw [he]
  simpa only [A, Coeff.reflection.norm_map, Complex.ofReal_pow] using!
    (inner_self_eq_norm_sq_to_K A)

theorem exists_hillSobolevRemainder_derivative_absorption (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      (∫ x in (0 : ℝ)..1, ‖sobolevPolynomialField m (hillReducedPolynomial m hm) (a,0)
        (x : AddCircle (2 : ℝ))‖) ≤ ε*‖hierarchySobolevJetL2 m m le_rfl a‖^2+
          C*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) := by
  let P : ℝ := 2^(2*m)
  have hP : 0 < P := by positivity
  obtain ⟨C,hC,hbound⟩ := exists_hillSobolevRemainder_Hm_absorption m hm (ε/P) (div_pos hε hP)
  refine ⟨ε+C,add_nonneg hε.le hC,?_⟩
  intro a
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖
  let J := ‖hierarchySobolevJetL2 m m le_rfl a‖
  have hhigh : ‖a‖^2 ≤ P*(A^2+J^2) := norm_sobolev_sq_le_highestJet m a
  calc
    _ ≤ (ε/P)*‖a‖^2+C*A^((4*m+6 : ℝ)/3) := hbound a
    _ ≤ (ε/P)*(P*(A^2+J^2))+C*A^((4*m+6 : ℝ)/3) := by gcongr
    _ = ε*J^2+ε*A^2+C*A^((4*m+6 : ℝ)/3) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hP.ne']
      ring
    _ ≤ _ := by
      change ε*J^2+ε*A^2+C*A^((4*m+6 : ℝ)/3) ≤
        ε*J^2+(ε+C)*(A^2+A^((4*m+6 : ℝ)/3))
      nlinarith [mul_nonneg hC (sq_nonneg A),
        mul_nonneg hε.le (show 0 ≤ A^((4*m+6 : ℝ)/3) by positivity)]

theorem exists_hillSobolevHamiltonian_energy_estimates (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      (∀ n, a.val (-n) = conj (a.val n)) →
      |2*(hillSobolevHamiltonian m hm a).re-‖hierarchySobolevJetL2 m m le_rfl a‖^2| ≤
        ε*‖hierarchySobolevJetL2 m m le_rfl a‖^2+
          C*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillSobolevRemainder_derivative_absorption m hm ε hε
  refine ⟨C,hC,?_⟩
  intro a ha
  have hr : ‖sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0)‖ ≤
      ε*‖hierarchySobolevJetL2 m m le_rfl a‖^2+
        C*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) := by
    rw [sobolevPolynomialMean_eq_physical_integral]
    exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (hbound a)
  have he : 2*(hillSobolevHamiltonian m hm a).re-
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2 =
      (sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0)).re := by
    rw [hillSobolevHamiltonian, hillSobolevKinetic_real m a ha]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re ]
    norm_num
    ring
  rw [he]
  exact (Complex.abs_re_le_norm _).trans hr

theorem exists_hillSobolevHamiltonian_coercivity (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      (∀ n, a.val (-n) = conj (a.val n)) →
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2 ≤ 4*(hillSobolevHamiltonian m hm a).re+
        C*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillSobolevHamiltonian_energy_estimates m hm (1/2) (by norm_num)
  refine ⟨2*C, mul_nonneg (by norm_num) hC,?_⟩
  intro a ha
  have h := (abs_le.mp (hbound a ha)).1
  nlinarith

theorem hill_fractional_error_le_polynomial (m : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    A^2+A^((4*m+6 : ℝ)/3) ≤ 2*(1+A^(2*m))*A^2 := by
  have hbase : A^2 ≤ (1+A^(2*m))*A^2 := by
    nlinarith [mul_nonneg (pow_nonneg hA (2*m)) (sq_nonneg A)]
  have hpower : A^((4*m+6 : ℝ)/3) ≤ (1+A^(2*m))*A^2 := by
    by_cases hsmall : A ≤ 1
    · have h := Real.rpow_le_rpow_of_exponent_ge' hA hsmall (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ (4*m+6)/3 by have := Nat.cast_nonneg (α := ℝ) m; linarith)
      rw [Real.rpow_two] at h
      exact h.trans hbase
    · have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ A)
        (show (4*m+6 : ℝ)/3 ≤ (2*m+2 : ℕ) by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) m])
      rw [Real.rpow_natCast, pow_add] at h
      nlinarith [sq_nonneg A]
  nlinarith

theorem exists_hillSobolevHamiltonian_polynomial_coercivity (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      (∀ n, a.val (-n) = conj (a.val n)) →
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2 ≤ 4*(hillSobolevHamiltonian m hm a).re+
        C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(2*m))*
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_hillSobolevHamiltonian_coercivity m hm
  refine ⟨2*C, mul_nonneg (by norm_num) hC,?_⟩
  intro a ha
  apply (hbound a ha).trans
  have h := mul_le_mul_of_nonneg_left
    (hill_fractional_error_le_polynomial m
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖ (norm_nonneg _)) hC
  nlinarith

theorem exists_hillSobolevHamiltonian_norm_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      ‖hillSobolevHamiltonian m hm a‖ ≤ ‖hierarchySobolevJetL2 m m le_rfl a‖^2+
        C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(2*m))*
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_hillSobolevRemainder_derivative_absorption m hm 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro a
  have hr : ‖sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0)‖ ≤
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2+
        C*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) := by
    rw [sobolevPolynomialMean_eq_physical_integral]
    simpa only [one_mul] using
      (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (hbound a)
  have hk : ‖sobolevOddKinetic m (a,a)‖ ≤ ‖hierarchySobolevJetL2 m m le_rfl a‖^2 := by
    simpa only [sobolevOddKinetic, Coeff.reflection.norm_map, pow_two] using
      Coeff.norm_dualPairing_le (Coeff.reflection (hierarchySobolevJetL2 m m le_rfl a))
        (hierarchySobolevJetL2 m m le_rfl a)
  have ht := norm_add_le (sobolevOddKinetic m (a,a))
    (sobolevPolynomialMean m (hillReducedPolynomial m hm) (a,0))
  have hp := mul_le_mul_of_nonneg_left
    (hill_fractional_error_le_polynomial m
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖ (norm_nonneg _)) hC
  rw [hillSobolevHamiltonian, norm_mul]
  norm_num
  nlinarith

end NLS.KdV
