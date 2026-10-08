import NLS.ZakharovShabat.SobolevRealJets
import NLS.ZakharovShabat.SobolevOddHamiltonianTrace
import NLS.ZakharovShabat.SourceRealHigherAction

/-! # The real physical odd Hamiltonian on H^m

Corollary H.2 holds for every real Sobolev source: the leading term is the
squared L² norm of the mth derivative. The actual higher-action trace proves
that the full Hamiltonian is real and nonnegative, hence its remainder mean
is real as well.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Real-type Sobolev sources have the original conjugate-reflection coefficients. -/
theorem realTypeHigherSobolevSource_coefficients (m : ℕ)
    (a : realTypeHigherSobolevSourceLocus m) (n : ℤ) :
    a.val.2.val n = conj (a.val.1.val (-n)) := by
  have h := a.property n
  change (higherSobolevSourceInclusion m a.val).snd n =
    conj ((higherSobolevSourceInclusion m a.val).fst (-n)) at h
  simpa only [higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd] using h

/-- The leading real physical pairing is exactly a squared L² derivative norm. -/
theorem sobolevOddKinetic_real (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) :
    sobolevOddKinetic m a.val = (‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 : ℝ) := by
  rw [sobolevOddKinetic,hierarchySobolevJetL2_real m m le_rfl a.val.1 a.val.2
    (realTypeHigherSobolevSource_coefficients m a)]
  let A := Coeff.reflection (hierarchySobolevJetL2 m m le_rfl a.val.1)
  have he : Coeff.dualPairing A (star A) = inner ℂ A A := by
    rw [Coeff.dualPairing_apply,lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    rw [RCLike.inner_apply',lp.star_apply,mul_comm]
    rfl
  change Coeff.dualPairing A (star A) = _
  rw [he]
  simpa only [A,Coeff.reflection.norm_map,Complex.ofReal_pow] using!
    (inner_self_eq_norm_sq_to_K A)

/-- The real H^m version of Corollary H.2, with the actual lower-jet physical mean. -/
theorem sobolevOddHamiltonian_real_decomposition (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    sobolevOddHamiltonian m hm a.val =
      (‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 : ℝ)+
        sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) a.val := by
  rw [sobolevOddHamiltonian,sobolevOddKinetic_real]

/-- An exact real series representation, retaining the physical definition of H. -/
theorem sobolevOddHamiltonian_eq_real_action_sum (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    sobolevOddHamiltonian m hm a.val = ((4:ℝ)^m * ∑' n : ℤ,
      sourceRealHigherAction (by simp) (by norm_num)
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n (2*m) : ℝ) := by
  have h := sobolevOddHamiltonian_higherAction_trace m hm a
  simp only [sourceComplexHigherAction_eq_real (φ :=
    (⟨higherSobolevSourceInclusion m a.val,a.property⟩ : realTypeSourceSubmodule 2)),
    ← Complex.ofReal_tsum] at h
  have h4 : (4:ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := (eq_div_iff h4).mp h
  rw [← he]
  push_cast
  ring

theorem sobolevOddHamiltonian_im_zero (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) : (sobolevOddHamiltonian m hm a.val).im = 0 := by
  rw [sobolevOddHamiltonian_eq_real_action_sum]
  exact Complex.ofReal_im _

/-- Positivity follows from the actual nonnegative odd-level actions. -/
theorem sobolevOddHamiltonian_real_nonneg (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) : 0 ≤ (sobolevOddHamiltonian m hm a.val).re := by
  rw [sobolevOddHamiltonian_eq_real_action_sum,Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (tsum_nonneg (fun n => sourceRealHigherAction_even_nonneg (by simp) (by norm_num) _ n m))

/-- The reduced remainder mean is real even for nonsmooth H^m data. -/
theorem sobolevOddRemainder_im_zero (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) a.val).im = 0 := by
  have h := sobolevOddHamiltonian_im_zero m hm a
  rw [sobolevOddHamiltonian_real_decomposition] at h
  simpa only [Complex.add_im,Complex.ofReal_im,zero_add] using h

end NLS.ZakharovShabat
