import NLS.KdV.PeriodOneHamiltonianVariation
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts

/-! The ACTUAL normalized variational gradient and Gardner vector field of
the physical KdV Hamiltonian, retaining q_t=-q_xxx+6*q*q_x. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

def classicalKdVGradient (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  -iteratedDeriv 2 q x+3*(q x)^2

def classicalKdVVectorField (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  -iteratedDeriv 3 q x+6*q x*deriv q x

theorem hasDerivAt_classicalKdVGradient (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (x : ℝ) :
    HasDerivAt (classicalKdVGradient q) (classicalKdVVectorField q x) x := by
  have hq' := (contDiff_infty_iff_deriv.mp hq).1 x
  have h2 := (NLS.FunctionalAnalysis.contDiff_iteratedDeriv q hq 2).differentiable (by norm_num) x
  have hd2 : HasDerivAt (iteratedDeriv 2 q) (iteratedDeriv 3 q x) x := by
    simpa only [show 3=2+1 by norm_num,iteratedDeriv_succ] using h2.hasDerivAt
  have hs := hd2.neg.add ((hq'.hasDerivAt.pow 2).const_mul (3:ℂ))
  have hv : -iteratedDeriv 3 q x+3*((2:ℂ)*q x^(2-1)*deriv q x)=classicalKdVVectorField q x := by
    norm_num [classicalKdVVectorField]
    ring
  norm_num only [Nat.cast_ofNat] at hs
  rw [hv] at hs
  simpa only [classicalKdVGradient] using! hs

theorem deriv_classicalKdVGradient (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) :
    deriv (classicalKdVGradient q)=classicalKdVVectorField q := by
  funext x
  exact (hasDerivAt_classicalKdVGradient q hq x).deriv

theorem classicalKdVGradient_periodic (q : ℝ → ℂ) (hq : Function.Periodic q 1) :
    Function.Periodic (classicalKdVGradient q) 1 := by
  intro x
  rw [classicalKdVGradient,classicalKdVGradient,
    NLS.FunctionalAnalysis.periodic_iteratedDeriv q 1 hq 2 x,hq x]

/-- Smooth physical representatives identify the full H1 first variation
with the L2 pairing against the ACTUAL gradient -q_xx+3*q^2. -/
theorem hasDerivAt_periodOneKdVHamiltonian_gradient (q h : ScalarDomain 2)
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2:ℝ)))) :
    HasDerivAt (fun z : ℂ => periodOneKdVHamiltonian (q+z • h))
      (∫ x in (0:ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2:ℝ))*
        classicalKdVGradient (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x) 0 := by
  let Q := fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))
  let H := fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2:ℝ))
  have hQ : ContDiff ℝ ∞ (deriv Q) := (contDiff_infty_iff_deriv.mp hq).2
  have hpQ := periodOneSobolevSynthesis_periodic q
  have hpH := periodOneSobolevSynthesis_periodic h
  have hibp := NLS.FunctionalAnalysis.integral_deriv_mul_periodic H (deriv Q) hh hQ hpH
    (NLS.FunctionalAnalysis.periodic_deriv Q 1 hpQ)
  have hkin : (∫ x in (0:ℝ)..1, deriv Q x*deriv H x)=
      -(∫ x in (0:ℝ)..1, H x*deriv (deriv Q) x) := by
    simpa only [mul_comm] using hibp
  have he : (∫ x in (0:ℝ)..1, deriv Q x*deriv H x+3*(Q x)^2*H x)=
      ∫ x in (0:ℝ)..1, H x*classicalKdVGradient Q x := by
    have hi1 : IntervalIntegrable (fun x => deriv Q x*deriv H x) volume 0 1 :=
      (hQ.continuous.mul (contDiff_infty_iff_deriv.mp hh).2.continuous).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun x => (3:ℂ)*(Q x)^2*H x) volume 0 1 :=
      ((continuous_const.mul (hq.continuous.pow 2)).mul hh.continuous).intervalIntegrable 0 1
    have hi3 : IntervalIntegrable (fun x => -(H x*deriv (deriv Q) x)) volume 0 1 :=
      ((hh.continuous.mul (contDiff_infty_iff_deriv.mp hQ).2.continuous).neg).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hi1 hi2,hkin,← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add hi3 hi2]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [classicalKdVGradient,iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  have hv := hasDerivAt_periodOneKdVHamiltonian_integral q h
  change HasDerivAt _ (∫ x in (0:ℝ)..1, deriv Q x*deriv H x+3*(Q x)^2*H x) 0 at hv
  rw [he] at hv
  exact hv

end NLS.KdV
