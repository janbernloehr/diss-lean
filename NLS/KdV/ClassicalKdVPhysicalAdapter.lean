import NLS.KdV.ClassicalKdVConservation
import NLS.KdV.SmoothPeriodicKdVJet
import NLS.KdV.HillClosedCurveSourceCoefficients
import NLS.KdV.ClassicalL2PrimitiveAgreement

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.KdV

theorem closedKdVCurve_coefficients_eq (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩ = f ⟨1,by norm_num⟩)
    (Q : C(AddCircle (2 : ℝ),ℂ))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (he : ∀ x : Icc (0 : ℝ) 1, f x = Q (x.val : AddCircle (2 : ℝ))) :
    SpectralWeight.one.toCoeff (hillClosedCurveCoefficients f hf) = Fourier.continuousFourierCLM Q := by
  ext k
  have hint : IntervalIntegrable (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) volume 0 1 := (Q.continuous.comp (show Continuous (fun x : ℝ => (x : AddCircle (2 : ℝ))) by fun_prop)).intervalIntegrable 0 1
  by_cases hk : k % 2 = 0
  · have hk' : k = 2*(k/2) := by omega
    simp only [SpectralWeight.toCoeff_apply,Fourier.continuousFourierCLM_apply]
    rw [hk',hillClosedCurveCoefficients_even_apply,← Fourier.periodTwoCoefficient_circle,
      Fourier.periodTwoCoefficient_periodic_even _ hp hint,Fourier.periodOneCoefficient,
      ← Fourier.unitFourierCoefficient_eq_fourierCoeffOn]
    apply Fourier.unitFourierCoefficient_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩)] using
      he ⟨x,hx.1.le,hx.2⟩
  · have hleft := (Coeff.mem_paritySubspace 0 _).mp (hillClosedCurveCoefficients_mem_even f hf) k hk
    rw [hleft,Fourier.continuousFourierCLM_apply,← Fourier.periodTwoCoefficient_circle]
    have hk' : k = 2*(k/2)+1 := by omega
    rw [hk',Fourier.periodTwoCoefficient_periodic_odd _ hp hint]

/-- Ordinary pointwise smooth KdV, with time differentiability in the
continuous-function norm, satisfies the physical Fourier PDE definition.
The hypotheses contain the actual differential equation, never an invariant. -/
theorem isClassicalKdVTrajectory_of_physical
    (u : ℝ → RealPeriodOneHillPotential) (Q : ℝ → C(AddCircle (2 : ℝ),ℂ))
    (hsource : ∀ t, SpectralWeight.one.toCoeff (u t).val = Fourier.continuousFourierCLM (Q t))
    (htime : Differentiable ℝ Q)
    (hsmooth : ∀ t, ContDiff ℝ ∞ (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))))
    (hperiod : ∀ t, Function.Periodic (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))) 1)
    (hpde : ∀ t x : ℝ, deriv Q t (x : AddCircle (2 : ℝ)) =
      6*Q t (x : AddCircle (2 : ℝ))*deriv (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))) x-
        iteratedDeriv 3 (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))) x) :
    IsClassicalKdVTrajectory u := by
  intro t
  let f : ℝ → ℂ := fun x => Q t (x : AddCircle (2 : ℝ))
  let J := PeriodicKdVJet.ofSmooth f (hsmooth t) (hperiod t)
  have hJ := closedKdVCurve_coefficients_eq J.value J.periodic_value.symm (Q t) (hperiod t)
    (fun x => by simp only [J,PeriodicKdVJet.ofSmooth,smoothKdVJetCurve,ContinuousMap.coe_mk,iteratedDeriv_zero]; rfl)
  have hpv : Function.Periodic (fun x : ℝ => deriv Q t (x : AddCircle (2 : ℝ))) 1 := by
    intro x
    change deriv Q t ((x+1 : ℝ) : AddCircle (2 : ℝ)) = deriv Q t (x : AddCircle (2 : ℝ))
    rw [hpde t (x+1),hpde t x]
    change 6*f (x+1)*deriv f (x+1)-iteratedDeriv 3 f (x+1) =
      6*f x*deriv f x-iteratedDeriv 3 f x
    have hpf : f (x+1) = f x := hperiod t x
    rw [hpf,periodic_deriv f 1 (hperiod t) x,periodic_iteratedDeriv f 1 (hperiod t) 3 x]
  have hV := closedKdVCurve_coefficients_eq J.velocity J.velocity_periodic.symm
    (deriv Q t) hpv (fun x => by
      rw [PeriodicKdVJet.ofSmooth_velocity,hpde t x.val])
  refine ⟨J,(hsource t).trans hJ.symm,?_⟩
  let hd := (Fourier.continuousFourierCLM).restrictScalars ℝ
  have hh := hd.hasFDerivAt.comp_hasDerivAt t ((htime t).hasDerivAt)
  have he : (fun τ => SpectralWeight.one.toCoeff (u τ).val) =
      fun τ => Fourier.continuousFourierCLM (Q τ) := funext hsource
  change SpectralWeight.one.toCoeff J.velocityCoefficients = Fourier.continuousFourierCLM (deriv Q t) at hV
  rw [he,hV]
  simpa only [hd,Function.comp_def,ContinuousLinearMap.coe_restrictScalars] using! hh

end NLS.KdV
