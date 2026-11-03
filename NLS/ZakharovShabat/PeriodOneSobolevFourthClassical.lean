import NLS.ZakharovShabat.PeriodOneSobolevFourthHamiltonian

/-! # Calibration of the fractional fourth Hamiltonian

For every smooth periodic physical pair with the specified Fourier coefficients,
the H^(3/2) polynomial is exactly the independent Riccati Hamiltonian H₄.
-/
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem fourth_coefficient_eq_unit (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient f n = periodOneCoefficient f n :=
  unitFourierCoefficient_eq_fourierCoeffOn f n

/-- Physical cubic coefficients retain the actual smooth product. -/
theorem fourthSobolevCubic_eq_classical_coefficients
    (ab : FourthSobolevSource) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) (n : ℤ) :
    fourthSobolevCubic ab n = periodOneCoefficient (f*(f*g)) n := by
  simp only [fourthSobolevCubic,WeightedCoeff.sobolevToL2_apply,
    hierarchySobolevTriple_apply,fourthSobolevToH1_apply,ha,hb]
  rw [periodOneCoefficient_mul_of_smooth_periodic f (f*g) hf (hf.mul hg) hpf (hpf.mul hpg)]
  apply tsum_congr
  intro j
  rw [periodOneCoefficient_mul_of_smooth_periodic f g hf hg hpf hpg]

/-- The distributional leading pairing equals its physical integral on smooth fields. -/
theorem fourthSobolev_leading_eq_classical_integral
    (ab : FourthSobolevSource) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) :
    WeightedCoeff.sobolevBilinearPairing (3/2) ab.1 (fourthSobolevThirdDerivative ab.2) =
      ∫ x in (0:ℝ)..1, f x*deriv (deriv (deriv g)) x := by
  have hdg := (contDiff_infty_iff_deriv.mp hg).2
  have hddg := (contDiff_infty_iff_deriv.mp hdg).2
  have hdddg := (contDiff_infty_iff_deriv.mp hddg).2
  have hpdg := periodic_deriv_of_periodic g 1 hpg
  have hpddg := periodic_deriv_of_periodic (deriv g) 1 hpdg
  have hc (j : ℤ) : (fourthSobolevThirdDerivative ab.2).val j =
      periodOneCoefficient (deriv (deriv (deriv g))) j := by
    rw [fourthSobolevThirdDerivative_apply,hb,
      periodOneCoefficient_deriv_of_smooth_periodic _ hddg hpddg,
      periodOneCoefficient_deriv_of_smooth_periodic _ hdg hpdg,
      periodOneCoefficient_deriv_of_smooth_periodic _ hg hpg]
    ring
  rw [WeightedCoeff.sobolevBilinearPairing_apply]
  simp_rw [ha,hc]
  rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ =>
    periodOneCoefficient f j*periodOneCoefficient (deriv (deriv (deriv g))) (-j))]
  simp only [Equiv.neg_apply,neg_neg]
  convert tsum_bilinear_unitFourierCoefficient hf.continuous hdddg.continuous using 1
  simp only [fourth_coefficient_eq_unit]

/-- The nonlinear pairing is the original physical a²bb' integral. -/
theorem fourthSobolev_quartic_eq_classical_integral
    (ab : FourthSobolevSource) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) :
    Coeff.dualPairing (Coeff.reflection (fourthSobolevCubic ab))
      (fourthSobolevFirstDerivative ab.2) =
        ∫ x in (0:ℝ)..1, f x^2*g x*deriv g x := by
  have hdg := (contDiff_infty_iff_deriv.mp hg).2
  rw [Coeff.dualPairing_apply]
  simp only [Coeff.reflection_apply,fourthSobolevFirstDerivative_apply,hb,
    fourthSobolevCubic_eq_classical_coefficients ab f g hf hg hpf hpg ha hb]
  have hc (j : ℤ) : 2*I*(Real.pi:ℂ)*j*periodOneCoefficient g j =
      periodOneCoefficient (deriv g) j :=
    (periodOneCoefficient_deriv_of_smooth_periodic g hg hpg j).symm
  simp_rw [hc]
  have hi := tsum_bilinear_unitFourierCoefficient
    (hf.continuous.mul (hf.continuous.mul hg.continuous)) hdg.continuous
  simp only [fourth_coefficient_eq_unit] at hi
  rw [hi]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Pi.mul_apply]
  ring

/-- Exact physical normalization at every smooth periodic pair, independently
of any spectral or Birkhoff definition. -/
theorem periodOneSobolevFourthHamiltonian_eq_classical
    (ab : FourthSobolevSource) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (ha : ∀ j, ab.1.val j = periodOneCoefficient f j)
    (hb : ∀ j, ab.2.val j = periodOneCoefficient g j) :
    periodOneSobolevFourthHamiltonian ab = classicalNLSHamiltonian f g 4 := by
  have hdg := (contDiff_infty_iff_deriv.mp hg).2
  have hddg := (contDiff_infty_iff_deriv.mp hdg).2
  have hdddg := (contDiff_infty_iff_deriv.mp hddg).2
  rw [periodOneSobolevFourthHamiltonian,
    fourthSobolev_leading_eq_classical_integral ab f g hf hg hpg ha hb,
    fourthSobolev_quartic_eq_classical_integral ab f g hf hg hpf hpg ha hb,
    classicalNLSHamiltonian_four f g hf hg hpf hpg]
  congr 1
  have hiA : IntervalIntegrable (fun x => f x*deriv (deriv (deriv g)) x) volume 0 1 :=
    (hf.continuous.mul hdddg.continuous).intervalIntegrable 0 1
  have hiB : IntervalIntegrable (fun x => (3:ℂ)*(f x^2*g x*deriv g x)) volume 0 1 :=
    (continuous_const.mul (((hf.continuous.pow 2).mul hg.continuous).mul hdg.continuous)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub hiA hiB]
  apply intervalIntegral.integral_congr
  intro x _
  ring

end NLS.ZakharovShabat
