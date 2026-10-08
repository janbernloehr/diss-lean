import NLS.ZakharovShabat.SobolevRemainderAbsorption
import NLS.ZakharovShabat.SobolevHighestJetEnergy

/-! # Lemma 26.3: the L²-only odd Hamiltonian remainder estimate

For every positive ε the actual absolute physical remainder integral is at
most ε times the highest derivative energy plus C(1+‖ψ‖₂^(4m))‖ψ‖₂².
The constants are uniform over all real H^m sources. The physical Hamiltonian
therefore obeys both the stated upper bound and a coercive lower bound.
-/
noncomputable section
open NLS.Fourier MeasureTheory
namespace NLS.ZakharovShabat

/-- Lemma 26.3, with the actual absolute remainder integral and an L²-only error. -/
theorem exists_sobolevOddRemainder_derivative_absorption (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (∫ x in (0:ℝ)..1, ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
        (x : AddCircle (2:ℝ))‖) ≤ ε*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
        C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2 := by
  let P : ℝ := 2^(2*m)
  have hP : 0 < P := by positivity
  obtain ⟨C,hC,hbound⟩ := exists_sobolevOddRemainder_Hm_absorption m hm (ε/P) (div_pos hε hP)
  refine ⟨ε+C,add_nonneg hε.le hC,?_⟩
  intro a
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖
  let J := ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖
  have hhigh : ‖a.val.1‖^2 ≤ P*(A^2+J^2) := norm_sobolev_sq_le_highestJet m a.val.1
  calc
    _ ≤ (ε/P)*‖a.val.1‖^2+C*A^(4*m+2) := hbound a
    _ ≤ (ε/P)*(P*(A^2+J^2))+C*A^(4*m+2) := by gcongr
    _ = ε*J^2+ε*A^2+C*A^(4*m+2) := by rw [← mul_assoc,div_mul_cancel₀ _ hP.ne']; ring
    _ ≤ _ := by
      change ε*J^2+ε*A^2+C*A^(4*m+2) ≤ ε*J^2+(ε+C)*(1+A^(4*m))*A^2
      rw [pow_add]
      have hA : 0 ≤ A := norm_nonneg _
      nlinarith [mul_nonneg hC (sq_nonneg A),mul_nonneg hε.le (mul_nonneg (pow_nonneg hA (4*m)) (sq_nonneg A))]

/-- The remainder bound controls both deviation from the kinetic term and
the absolute Hamiltonian, with the same source-independent constant. -/
theorem exists_sobolevOddHamiltonian_energy_estimates (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (|(sobolevOddHamiltonian m hm a.val).re-‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2| ≤
        ε*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
          C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2) ∧
      (‖sobolevOddHamiltonian m hm a.val‖ ≤
        (1+ε)*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
          C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2) := by
  obtain ⟨C,hC,hbound⟩ := exists_sobolevOddRemainder_derivative_absorption m hm ε hε
  refine ⟨C,hC,?_⟩
  intro a
  have hr : ‖sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) a.val‖ ≤
      ε*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2+
        C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2 := by
    rw [sobolevPolynomialMean_eq_physical_integral]
    exact (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (hbound a)
  constructor
  · rw [sobolevOddHamiltonian_real_decomposition,Complex.add_re,Complex.ofReal_re,add_sub_cancel_left]
    exact (Complex.abs_re_le_norm _).trans hr
  · rw [sobolevOddHamiltonian_real_decomposition]
    have h := norm_add_le ((‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 : ℝ) : ℂ)
      (sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) a.val)
    simp only [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)] at h
    nlinarith

/-- Fixing ε=1/2 gives a uniform lower bound controlling the highest derivative
by the physical Hamiltonian and the same L²-only error. -/
theorem exists_sobolevOddHamiltonian_coercivity (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 ≤ 2*(sobolevOddHamiltonian m hm a.val).re+
        C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
          ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm (1/2) (by norm_num)
  refine ⟨2*C,mul_nonneg (by norm_num) hC,?_⟩
  intro a
  have h := (abs_le.mp (hbound a).1).1
  nlinarith

end NLS.ZakharovShabat
