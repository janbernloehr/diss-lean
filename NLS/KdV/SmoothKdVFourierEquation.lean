import NLS.KdV.KdVFourierField
import NLS.KdV.ClassicalKdVUniqueness
import NLS.Fourier.PeriodOneFourierUniqueness

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open scoped ContDiff
namespace NLS.KdV

theorem kdvUnitFourierCLM_eq_periodOneCoefficient
    (Q : C(AddCircle (2 : ℝ),ℂ))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1) (n : ℤ) :
    kdvUnitFourierCLM Q n =
      Fourier.periodOneCoefficient (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) n := by
  rw [kdvUnitFourierCLM_apply,← Fourier.periodTwoCoefficient_circle,
    Fourier.periodTwoCoefficient_periodic_even _ hp]
  exact (Q.continuous.comp (show Continuous (fun x : ℝ => (x : AddCircle (2 : ℝ))) by
    fun_prop)).intervalIntegrable 0 1

/-- The Fourier field is identified with the actual physical differential
operator, including the nonlinear product and every integer frequency. -/
theorem periodOneCoefficient_scalarClassicalKdVField (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (a : Coeff 2) (ha : ∀ n, a n = Fourier.periodOneCoefficient f n) (n : ℤ) :
    Fourier.periodOneCoefficient (scalarClassicalKdVField f) n = kdvFourierModeField a n := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hf3 := (contDiff_infty_iff_deriv.mp hf2).2
  have hp1 := ZakharovShabat.periodic_deriv_of_periodic f 1 hp
  have hp2 := ZakharovShabat.periodic_deriv_of_periodic (deriv f) 1 hp1
  have hprod : deriv (f*f) = fun x => 2*f x*deriv f x := by
    funext x
    convert (((contDiff_infty_iff_deriv.mp hf).1 x).hasDerivAt.mul
      ((contDiff_infty_iff_deriv.mp hf).1 x).hasDerivAt).deriv using 1
    ring
  have he : scalarClassicalKdVField f = (fun x => 3*deriv (f*f) x)-deriv (deriv (deriv f)) := by
    rw [hprod]
    funext x
    dsimp [scalarClassicalKdVField]
    ring
  have hc : Continuous (fun x => (3:ℂ)*deriv (f*f) x) :=
    continuous_const.mul (contDiff_infty_iff_deriv.mp (hf.mul hf)).2.continuous
  rw [he,Fourier.periodOneCoefficient_sub _ _ hc hf3.continuous,
    Fourier.periodOneCoefficient_const_mul,
    Fourier.periodOneCoefficient_deriv_of_smooth_periodic (f*f) (hf.mul hf) (hp.mul hp),
    Fourier.periodOneCoefficient_mul_of_smooth_periodic f f hf hf hp hp,
    Fourier.periodOneCoefficient_deriv_of_smooth_periodic _ hf2 hp2,
    Fourier.periodOneCoefficient_deriv_of_smooth_periodic _ hf1 hp1,
    Fourier.periodOneCoefficient_deriv_of_smooth_periodic _ hf hp]
  simp only [kdvFourierModeField,kdvQuadraticMode_eq_tsum,ha]
  ring

/-- Independent spatially weak, time-integrated Fourier KdV equation on
continuous physical profiles. No classical-approximation or invariant
condition is part of the definition. -/
def IsFourierWeakPhysicalKdV (Q : ℝ → C(AddCircle (2 : ℝ),ℂ)) : Prop :=
  IsFourierWeakKdVCoefficients (fun t => kdvUnitFourierCLM (Q t))

end NLS.KdV
