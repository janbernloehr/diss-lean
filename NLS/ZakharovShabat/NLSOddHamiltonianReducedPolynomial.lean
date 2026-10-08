import Mathlib.Analysis.Calculus.Deriv.Star
import NLS.DifferentialPolynomial.BalancedJetProduct
import NLS.ZakharovShabat.NLSRiccatiPolynomialRemainder

/-! # The smooth periodic polynomial reduction of Corollary H.2

For every positive m, one polynomial in jets through order m-1 represents
the nonlinear part of H_(2m+1) on every smooth periodic pair. The leading
term is the pairing of the mth derivatives. Total weight and field balance
are preserved. Extension to H^m is a separate analytic step.
-/
noncomputable section
open MvPolynomial NLS.DifferentialPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Appendix H's nonlinear odd density is reduced modulo a total derivative. -/
theorem exists_nlsOddRemainder_jet_reduction (m : ℕ) (hm : 1 ≤ m) :
    HasJetReduction m (2*(m:ℤ)+2) 0 (2*(m:ℤ)-2) (X (false,0)*nlsRiccatiRemainder (2*m)) := by
  obtain ⟨hw,hc,hd⟩ := nlsRiccatiRemainder_hamiltonian_grades (2*m)
  apply exists_graded_jet_reduction m hm
  · simpa using hw
  · exact hc
  · simpa using hd

private theorem oddHamiltonian_phase (m : ℕ) :
    (-Complex.I)^(2*m+2) * (-(-1:ℂ)^m) = 1 := by
  rw [pow_add,pow_mul]
  have hsq : (-Complex.I)^2 = (-1:ℂ) := by norm_num [Complex.I_sq]
  rw [hsq]
  calc
    (-1:ℂ)^m * (-1) * -(-1:ℂ)^m = (-1:ℂ)^m*(-1:ℂ)^m := by ring
    _ = ((-1:ℂ)*(-1))^m := (mul_pow _ _ _).symm
    _ = 1 := by norm_num

/-- The original Hamiltonian is the balanced leading integral plus its
independently defined nonlinear differential-polynomial integral. -/
theorem classicalNLSHamiltonian_odd_leading_remainder (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (m : ℕ) :
    classicalNLSHamiltonian a b (2*m+1) =
      (∫ x in (0:ℝ)..1, iteratedDeriv m a x*iteratedDeriv m b x) +
      (-Complex.I)^(2*m+2) * ∫ x in (0:ℝ)..1,
        evaluate a b (X (false,0)*nlsRiccatiRemainder (2*m)) x := by
  have hlead : Continuous (fun x => a x*iteratedDeriv (2*m) b x) :=
    ha.continuous.mul (hb.continuous_iteratedDeriv (2*m) (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))
  have hrem := continuous_evaluate a b ha hb (X (false,0)*nlsRiccatiRemainder (2*m))
  rw [classicalNLSHamiltonian,nlsRiccatiDensity_eq_leading_add_remainder a b ha hb]
  have he : (fun x => a x*(-iteratedDeriv (2*m) b+evaluate a b (nlsRiccatiRemainder (2*m))) x) =
      (fun x => -(a x*iteratedDeriv (2*m) b x)+
        evaluate a b (X (false,0)*nlsRiccatiRemainder (2*m)) x) := by
    funext x
    simp
    ring
  have hneg : IntervalIntegrable (fun x => -(a x*iteratedDeriv (2*m) b x)) volume 0 1 := by
    simpa only [Pi.neg_apply] using! hlead.neg.intervalIntegrable (μ := volume) 0 1
  rw [he,intervalIntegral.integral_add hneg (hrem.intervalIntegrable 0 1),
    intervalIntegral.integral_neg,integral_balanced_derivatives a b ha hb hpa hpb]
  have hphase := oddHamiltonian_phase m
  linear_combination hphase * (∫ x in (0:ℝ)..1, iteratedDeriv m a x*iteratedDeriv m b x)

/-- One lower-order remainder polynomial works for all smooth periodic fields.
Its weight and field balance are exactly those in Corollary H.2. -/
theorem exists_classicalNLSHamiltonian_odd_reduced_polynomial (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m:ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        Function.Periodic a 1 → Function.Periodic b 1 →
        classicalNLSHamiltonian a b (2*m+1) = ∫ x in (0:ℝ)..1,
          iteratedDeriv m a x*iteratedDeriv m b x+evaluate a b q x := by
  obtain ⟨q,r,he,hq,hw,hc,_⟩ := exists_nlsOddRemainder_jet_reduction m hm
  let z : ℂ := (-Complex.I)^(2*m+2)
  have hC : JetOrderLE (C z) (m-1) := Supported.monomial 0 z (by simp)
  refine ⟨C z*q,hC.mul hq,hw.C_mul z,hc.C_mul z,?_⟩
  intro a b ha hb hpa hpb
  rw [classicalNLSHamiltonian_odd_leading_remainder a b ha hb hpa hpb,
    integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ q r he]
  have hlead : Continuous (fun x => iteratedDeriv m a x*iteratedDeriv m b x) :=
    (ha.continuous_iteratedDeriv _ (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)).mul
      (hb.continuous_iteratedDeriv _ (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))
  rw [intervalIntegral.integral_add (hlead.intervalIntegrable 0 1)
    ((continuous_evaluate a b ha hb (C z*q)).intervalIntegrable 0 1)]
  simp only [evaluate_mul,evaluate_C,Pi.mul_apply,intervalIntegral.integral_const_mul]
  rfl

/-- On real-type smooth pairs, the balanced leading term is the squared norm
of the mth derivative, as in Corollary H.2. -/
theorem exists_classicalNLSHamiltonian_odd_real_reduced_polynomial (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m:ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → Function.Periodic f 1 →
        classicalNLSHamiltonian f (fun x => star (f x)) (2*m+1) = ∫ x in (0:ℝ)..1,
          (‖iteratedDeriv m f x‖^2 : ℝ)+evaluate f (fun y => star (f y)) q x := by
  obtain ⟨q,hq,hw,hc,ht⟩ := exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm
  refine ⟨q,hq,hw,hc,?_⟩
  intro f hf hp
  have hps : Function.Periodic (fun x => star (f x)) 1 := fun x => congrArg star (hp x)
  rw [ht f (fun x => star (f x)) hf (Complex.conjCLE.contDiff.comp hf) hp hps]
  have he (n : ℕ) : iteratedDeriv n (fun x => star (f x)) = fun x => star (iteratedDeriv n f x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iteratedDeriv_succ,ih,deriv.star',← iteratedDeriv_succ]
  apply intervalIntegral.integral_congr
  intro x _
  rw [he]
  simp [Complex.mul_conj,Complex.normSq_eq_norm_sq]

end NLS.ZakharovShabat
