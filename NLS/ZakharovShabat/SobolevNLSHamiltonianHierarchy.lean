import NLS.ZakharovShabat.SobolevRiccatiHierarchy
import NLS.SequenceSpaces.ConjugateDuality
import NLS.ZakharovShabat.PeriodOneSobolevMomentum

/-! # Analytic Hamiltonians from the Sobolev Riccati recurrence

The unit-period mean is the bounded bilinear Fourier pairing. Thus Appendix H's
normalization gives an entire analytic Hamiltonian of order k on Hˢ whenever
k ≤ s+1. These definitions use differentiation and physical products only.
-/
noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- The physical Riccati hierarchy, indexed by the positive Hamiltonian order.
The order-zero value is zero, as in `classicalNLSHamiltonian`. -/
def sobolevNLSHamiltonian (s : ℕ) (ab : SobolevSource s) : (k : ℕ) → k ≤ s+1 → ℂ
  | 0, _ => 0
  | n+1, hn => (-I)^(n+2) * Coeff.dualPairing
      (Coeff.reflection (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) ab.1))
      (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-n))
        (sobolevRiccatiDensity s ab n (by omega)))

@[simp] theorem sobolevNLSHamiltonian_zero (s : ℕ) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s ab 0 (by omega) = 0 := rfl

/-- The original Fourier coefficients give the absolutely convergent mean
of the physical Riccati density, with Appendix H's factor `(-i)^(n+2)`. -/
theorem sobolevNLSHamiltonian_succ_eq_tsum (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s ab (n+1) (by omega) =
      (-I)^(n+2) * ∑' j : ℤ, ab.1.val (-j) * (sobolevRiccatiDensity s ab n hn).val j := by
  simp only [sobolevNLSHamiltonian,Coeff.dualPairing_apply,Coeff.reflection_apply,
    WeightedCoeff.sobolevToL2_apply]

/-- Hölder ensures absolute convergence of the physical density mean. -/
theorem summable_norm_sobolevRiccatiMean (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) :
    Summable (fun j : ℤ => ‖ab.1.val (-j)*(sobolevRiccatiDensity s ab n hn).val j‖) := by
  simpa only [Coeff.reflection_apply,WeightedCoeff.sobolevToL2_apply] using
    Coeff.summable_norm_dualPairing
      (Coeff.reflection (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) ab.1))
      (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-n)) (sobolevRiccatiDensity s ab n hn))

/-- Every Hamiltonian in the admissible regularity range is entire complex analytic. -/
theorem analyticAt_sobolevNLSHamiltonian (s k : ℕ) (hk : k ≤ s+1) (ab : SobolevSource s) :
    AnalyticAt ℂ (fun cd => sobolevNLSHamiltonian s cd k hk) ab := by
  rcases k with _ | n
  · exact analyticAt_const
  · let A : SobolevSource s →L[ℂ] Coeff 2 :=
      (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s))).comp (ContinuousLinearMap.fst ℂ _ _)
    have hD := ((WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-n))).analyticAt _).comp
      (analyticAt_sobolevRiccatiDensity s n (by omega) ab)
    exact analyticAt_const.mul ((Coeff.dualPairing.analyticAt_bilinear _).comp
      (f := fun cd => (A cd,WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-n))
        (sobolevRiccatiDensity s cd n (by omega)))) ((A.analyticAt ab).prod hD))

theorem continuous_sobolevNLSHamiltonian (s k : ℕ) (hk : k ≤ s+1) :
    Continuous (fun ab => sobolevNLSHamiltonian s ab k hk) :=
  continuous_iff_continuousAt.mpr fun ab => (analyticAt_sobolevNLSHamiltonian s k hk ab).continuousAt

/-- The first order is the original mass pairing, including the H⁰ endpoint. -/
theorem sobolevNLSHamiltonian_one (s : ℕ) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s ab 1 (by omega) = ∑' j : ℤ, ab.1.val (-j)*ab.2.val j := by
  rw [sobolevNLSHamiltonian_succ_eq_tsum s 0 (by omega)]
  simp only [sobolevRiccatiDensity_zero,WeightedCoeff.neg_val,mul_neg,tsum_neg]
  norm_num [I_sq]

/-- The second order is the period-one physical momentum with its exact sign. -/
theorem sobolevNLSHamiltonian_two (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s ab 2 (by omega) = ∑' j : ℤ,
      (2*(Real.pi:ℂ)*j)*ab.1.val (-j)*ab.2.val j := by
  rw [sobolevNLSHamiltonian_succ_eq_tsum s 1 hs,← tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [sobolevRiccatiDensity_one,WeightedCoeff.neg_val,hierarchySobolevDerivative_apply]
  norm_num [pow_succ,I_sq]
  ring_nf
  simp [I_sq]

/-- The general Riccati construction recovers the established H¹ physical mass. -/
theorem sobolevNLSHamiltonian_one_eq_periodOneSobolevMass (ab : ScalarDomain 2 × ScalarDomain 2) :
    sobolevNLSHamiltonian 1 (higherSobolevSourceOneEquiv ab) 1 (by norm_num) = periodOneSobolevMass ab := by
  rw [sobolevNLSHamiltonian_one,periodOneSobolevMass,Coeff.dualPairing_apply]
  apply tsum_congr
  intro j
  have h := higherSobolevSourceInclusion_one ab
  have h1 := congrArg (fun a : CoeffPair 2 => a.fst (-j)) h
  have h2 := congrArg (fun a : CoeffPair 2 => a.snd j) h
  simpa only [higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd,
    sobolevSourceInclusion_fst,sobolevSourceInclusion_snd,Coeff.reflection_apply,scalarInclusion_apply]
    using congrArg₂ (fun x y : ℂ => x*y) h1 h2

/-- The second order agrees with the established H¹ physical momentum. -/
theorem sobolevNLSHamiltonian_two_eq_periodOneSobolevMomentum (ab : ScalarDomain 2 × ScalarDomain 2) :
    sobolevNLSHamiltonian 1 (higherSobolevSourceOneEquiv ab) 2 (by norm_num) = periodOneSobolevMomentum ab := by
  rw [sobolevNLSHamiltonian_two 1 le_rfl,periodOneSobolevMomentum_eq_tsum]
  apply tsum_congr
  intro j
  have h := higherSobolevSourceInclusion_one ab
  have h1 := congrArg (fun a : CoeffPair 2 => a.fst (-j)) h
  have h2 := congrArg (fun a : CoeffPair 2 => a.snd j) h
  simp only [higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd,
    sobolevSourceInclusion_fst,sobolevSourceInclusion_snd] at h1 h2
  rw [h1,h2]

end NLS.ZakharovShabat
