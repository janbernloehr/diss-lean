import NLS.KdV.PeriodOneHamiltonian

/-! The actual physical KdV first variation on the ENTIRE complex H1
domain, with classical almost-everywhere derivatives on the unit interval. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem periodOneKdVHamiltonian_variation_eq_integral (q h : ScalarDomain 2) :
    periodOneSobolevKinetic (q,h)+
      periodOneCircleMean (3*(periodOneSobolevSynthesis q)^2*periodOneSobolevSynthesis h)=
        ∫ x in (0:ℝ)..1,
          deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x *
            deriv (fun y : ℝ => periodOneSobolevSynthesis h (y : AddCircle (2:ℝ))) x+
          3*(periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))^2*
            periodOneSobolevSynthesis h (x : AddCircle (2:ℝ)) := by
  have hp : Function.Periodic (fun x : ℝ =>
      ((3 : C(AddCircle (2:ℝ),ℂ))*(periodOneSobolevSynthesis q)^2*periodOneSobolevSynthesis h) (x : AddCircle (2:ℝ))) 1 := by
    intro x
    exact congrArg₂ (fun a b : ℂ => 3*a^2*b)
      (periodOneSobolevSynthesis_periodic q x) (periodOneSobolevSynthesis_periodic h x)
  rw [periodOneSobolevKinetic_eq_integral,periodOneCircleMean_eq_integral _ hp]
  have hk : IntervalIntegrable (fun x : ℝ =>
      deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x *
        deriv (fun y : ℝ => periodOneSobolevSynthesis h (y : AddCircle (2:ℝ))) x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_deriv_periodOneSobolevSynthesis q).integrable_mul (memLp_deriv_periodOneSobolevSynthesis h))
  have hc : IntervalIntegrable (fun x : ℝ =>
      3*(periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))^2*
        periodOneSobolevSynthesis h (x : AddCircle (2:ℝ))) volume 0 1 :=
    ((continuous_const.mul ((continuous_periodOneSobolevSynthesis q).pow 2)).mul
      (continuous_periodOneSobolevSynthesis h)).intervalIntegrable 0 1
  simpa using!
    (intervalIntegral.integral_add hk hc).symm

theorem hasDerivAt_periodOneKdVHamiltonian_integral (q h : ScalarDomain 2) :
    HasDerivAt (fun z : ℂ => periodOneKdVHamiltonian (q+z • h))
      (∫ x in (0:ℝ)..1,
        deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x *
          deriv (fun y : ℝ => periodOneSobolevSynthesis h (y : AddCircle (2:ℝ))) x+
        3*(periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))^2*
          periodOneSobolevSynthesis h (x : AddCircle (2:ℝ))) 0 := by
  rw [← periodOneKdVHamiltonian_variation_eq_integral]
  exact hasDerivAt_periodOneKdVHamiltonian q h

end NLS.KdV
