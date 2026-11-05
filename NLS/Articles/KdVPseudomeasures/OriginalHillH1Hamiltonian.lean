import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity
import NLS.KdV.PeriodOneHamiltonian

/-! The physical KdV Hamiltonian pulled back by the SAME canonical H1
inverse. Its native target is exactly signed H^(3/2). This constructs the
actual analytic energy, without assuming action dependence or a flow. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.KdVPseudomeasures

def signedOneRealToScalarDomain : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] ScalarDomain 2 :=
  ((weightedMultiplierCLM (Weight.signedSobolev (signedStepOrder 0 1)) (Weight.sobolev 1) (fun _ => 1)
    2 (by norm_num) (by
      intro k
      simp only [norm_one,mul_one,Weight.sobolev_apply,Weight.signedSobolev,signedStepOrder,zero_add,Real.rpow_one]
      have h1 := le_max_left (1:ℝ) |(k:ℝ)|
      have h2 := le_max_right (1:ℝ) |(k:ℝ)|
      linarith)).restrictScalars ℝ).comp
    (((zeroModeSubmodule (Weight.signedSobolev (signedStepOrder 0 1)) 2).subtypeL.restrictScalars ℝ).comp
      (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 1)) 2).subtypeL)

theorem signedOneRealToScalarDomain_apply (q : RealSignedHilbert (signedStepOrder 0 1)) (k : ℤ) :
    (signedOneRealToScalarDomain q).val k=q.val.val.val k := by
  change (1:ℂ)*q.val.val.val k=_
  exact one_mul _

def hillH1KdVHamiltonian (q : RealSignedHilbert (signedStepOrder 0 1)) : ℝ :=
  (periodOneKdVHamiltonian (signedOneRealToScalarDomain q)).re

theorem analyticAt_hillH1KdVHamiltonian (q : RealSignedHilbert (signedStepOrder 0 1)) :
    AnalyticAt ℝ hillH1KdVHamiltonian q := by
  have hL : AnalyticAt ℝ signedOneRealToScalarDomain q :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance
      (ScalarDomain 2) inferInstance inferInstance signedOneRealToScalarDomain q
  have hC : AnalyticAt ℝ periodOneKdVHamiltonian (signedOneRealToScalarDomain q) :=
    (analyticAt_periodOneKdVHamiltonian (signedOneRealToScalarDomain q)).restrictScalars
  have h : AnalyticAt ℝ (fun a => periodOneKdVHamiltonian (signedOneRealToScalarDomain a)) q := hC.comp hL
  exact (Complex.reCLM.analyticAt _).comp h

/-- The SAME actual native inverse defines the physical Hamiltonian on
ALL real signed H^(3/2), including closed gaps. -/
def hillH1CanonicalHamiltonian
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ℝ :=
  hillH1KdVHamiltonian ((hillIntegerSobolevEquiv 1).equiv.symm z)

theorem analyticAt_hillH1CanonicalHamiltonian
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    AnalyticAt ℝ hillH1CanonicalHamiltonian z :=
  (analyticAt_hillH1KdVHamiltonian _).comp ((hillIntegerSobolevEquiv 1).analytic_symm z)

theorem hillH1CanonicalHamiltonian_actual_coordinates
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillH1CanonicalHamiltonian ((hillIntegerSobolevEquiv 1).equiv q)=hillH1KdVHamiltonian q := by
  exact congrArg hillH1KdVHamiltonian ((hillIntegerSobolevEquiv 1).equiv.symm_apply_apply q)

theorem hillH1KdVHamiltonian_physical (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillH1KdVHamiltonian q=(∫ x in (0:ℝ)..1,
      (1/2:ℂ)*(deriv (fun y : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q)
        (y : AddCircle (2:ℝ))) x)^2+
        (periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ)))^3).re :=
  congrArg Complex.re (periodOneKdVHamiltonian_eq_integral (signedOneRealToScalarDomain q))

end NLS.Articles.KdVPseudomeasures
