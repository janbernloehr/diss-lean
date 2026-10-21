import NLS.ZakharovShabat.NLSOddHamiltonianReducedPolynomial
import NLS.ZakharovShabat.ClassicalHamiltonianSignCheck

/-! # The phase of the unreduced polynomial in Appendix H

The display between H.1 and H.2 needs the factor (-1)^(m+1) if q_(2m)
continues to denote the remainder fixed by H.1. The reduced polynomial
in H.2 can absorb this factor, so that corollary is unchanged.
-/
noncomputable section
open NLS.DifferentialPolynomial MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The phase fixed by the original Hamiltonian normalization. -/
theorem appendixH_odd_remainder_phase (m : ℕ) :
    (-Complex.I)^(2*m+2) = (-1 : ℂ)^(m+1) := by
  rw [show 2*m+2 = 2*(m+1) by omega, pow_mul]
  norm_num [Complex.I_sq]

/-- The smooth real formula with the exact remainder chosen in H.1. -/
theorem classicalNLSHamiltonian_odd_real_H1_remainder (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (m : ℕ) :
    classicalNLSHamiltonian f (fun x => star (f x)) (2*m+1) =
      (∫ x in (0 : ℝ)..1, (‖iteratedDeriv m f x‖^2 : ℝ)) +
      (-1 : ℂ)^(m+1) * ∫ x in (0 : ℝ)..1,
        f x * evaluate f (fun y => star (f y)) (nlsRiccatiRemainder (2*m)) x := by
  have hps : Function.Periodic (fun x => star (f x)) 1 := fun x => congrArg star (hp x)
  rw [classicalNLSHamiltonian_odd_leading_remainder f (fun x => star (f x))
    hf (Complex.conjCLE.contDiff.comp hf) hp hps, appendixH_odd_remainder_phase]
  have he (n : ℕ) : iteratedDeriv n (fun x => star (f x)) =
      fun x => star (iteratedDeriv n f x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iteratedDeriv_succ, ih, deriv.star', ← iteratedDeriv_succ]
  rw [he]
  congr 1
  · rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp

/-- At even m, omitting the phase is valid exactly when the unreduced integral vanishes. -/
theorem appendixH_even_unphased_formula_iff (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (m : ℕ) (hm : Even m) :
    (classicalNLSHamiltonian a b (2*m+1) =
      (∫ x in (0 : ℝ)..1, iteratedDeriv m a x*iteratedDeriv m b x) +
      ∫ x in (0 : ℝ)..1, evaluate a b (MvPolynomial.X (false,0)*nlsRiccatiRemainder (2*m)) x) ↔
      (∫ x in (0 : ℝ)..1, evaluate a b
        (MvPolynomial.X (false,0)*nlsRiccatiRemainder (2*m)) x) = 0 := by
  rw [classicalNLSHamiltonian_odd_leading_remainder a b ha hb hpa hpb,
    appendixH_odd_remainder_phase, pow_succ, hm.neg_one_pow]
  constructor
  · intro h
    linear_combination -h/2
  · intro h
    rw [h]
    simp only [mul_zero]

/-- The same q_4 from H.1 evaluates to -2 at the smooth real constant potential. -/
theorem appendixH_q4_constant_one :
    (∫ x in (0 : ℝ)..1,
      evaluate (fun _ => 1) (fun _ => 1) (nlsRiccatiRemainder 4) x) = (-2 : ℂ) := by
  have h := classicalNLSHamiltonian_odd_leading_remainder
    (fun _ => 1) (fun _ => 1) contDiff_const contDiff_const
    (fun _ => by rfl) (fun _ => by rfl) 2
  rw [show 2*2+1 = 5 by rfl, classicalNLSHamiltonian_constant_one_five] at h
  norm_num [evaluate_mul, evaluate_X, iteratedDeriv_succ, pow_succ] at h
  linear_combination h

/-- The intermediate printed display fails with the literal H.1 remainder at m=2. -/
theorem appendixH_unphased_display_counterexample :
    classicalNLSHamiltonian (fun _ => 1) (fun _ => 1) 5 ≠
      ∫ x in (0 : ℝ)..1,
        (‖iteratedDeriv 2 (fun _ : ℝ => (1 : ℂ)) x‖^2 : ℝ) +
        evaluate (fun _ => 1) (fun _ => 1) (nlsRiccatiRemainder 4) x := by
  simpa [iteratedDeriv_succ, classicalNLSHamiltonian_constant_one_five,
    appendixH_q4_constant_one] using (by norm_num : (2 : ℂ) ≠ -2)

end NLS.ZakharovShabat
