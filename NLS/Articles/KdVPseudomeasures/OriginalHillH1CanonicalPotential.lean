import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerFreeDerivative
import NLS.Articles.KdVPseudomeasures.OriginalHillH1FrequencyAnalytic

/-! The SAME canonical inverse regarded in the original physical H1
coefficient space, with its literal free derivative and native mode curves. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

def hillH1CanonicalPotential (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ScalarDomain 2 :=
  signedOneRealToScalarDomain ((hillIntegerSobolevEquiv 1).equiv.symm z)

theorem analyticAt_hillH1CanonicalPotential (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    AnalyticAt ℝ hillH1CanonicalPotential z := by
  have hS : AnalyticAt ℝ signedOneRealToScalarDomain ((hillIntegerSobolevEquiv 1).equiv.symm z) :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance
      (ScalarDomain 2) inferInstance inferInstance signedOneRealToScalarDomain _
  exact hS.comp ((hillIntegerSobolevEquiv 1).analytic_symm z)

theorem hillH1CanonicalPotential_zero : hillH1CanonicalPotential 0=0 := by
  simp only [hillH1CanonicalPotential,hillIntegerSobolevEquiv_symm_zero,map_zero]

theorem hillH1CanonicalHamiltonian_eq_physical (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    hillH1CanonicalHamiltonian z=(periodOneKdVHamiltonian (hillH1CanonicalPotential z)).re := rfl

theorem fderiv_hillH1CanonicalPotential_zero_apply
    (h : RealSignedHilbert (signedStepOrder (1/2) 1)) (k : ℤ) :
    ((fderiv ℝ hillH1CanonicalPotential 0) h).val k=halfFourierInverseSymbol k*h.val.val.val k := by
  have hd := @fderiv_clm_after_apply
    (RealSignedHilbert (signedStepOrder (1/2) 1)) (RealSignedHilbert (signedStepOrder 0 1))
    (ScalarDomain 2) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillIntegerSobolevEquiv 1).equiv.symm signedOneRealToScalarDomain 0 h
    ((hillIntegerSobolevEquiv 1).analytic_symm 0).differentiableAt
  have he := congrArg (fun q : ScalarDomain 2 => q.val k) hd
  simpa only [hillH1CanonicalPotential,signedOneRealToScalarDomain_apply,
    fderiv_hillIntegerSobolevEquiv_symm_zero_apply] using! he

def hillH1PhysicalModeCurve (n : ℕ+) (t : ℝ) : ScalarDomain 2 :=
  hillH1CanonicalPotential (t • hillH1ModeCLM n 1)

theorem analyticAt_hillH1PhysicalModeCurve (n : ℕ+) (t : ℝ) :
    AnalyticAt ℝ (hillH1PhysicalModeCurve n) t := by
  apply (analyticAt_hillH1CanonicalPotential _).comp
  exact analyticAt_id.smul analyticAt_const

theorem hillH1PhysicalModeCurve_zero (n : ℕ+) : hillH1PhysicalModeCurve n 0=0 := by
  simp only [hillH1PhysicalModeCurve,zero_smul,hillH1CanonicalPotential_zero]

theorem hasDerivAt_hillH1PhysicalModeCurve_zero (n : ℕ+) :
    HasDerivAt (hillH1PhysicalModeCurve n) ((fderiv ℝ hillH1CanonicalPotential 0) (hillH1ModeCLM n 1)) 0 :=
  @hasDerivAt_map_real_ray (RealSignedHilbert (signedStepOrder (1/2) 1)) (ScalarDomain 2)
    inferInstance inferInstance inferInstance inferInstance hillH1CanonicalPotential (hillH1ModeCLM n 1)
    (analyticAt_hillH1CanonicalPotential 0).differentiableAt

theorem deriv_hillH1PhysicalModeCurve_zero_apply (n : ℕ+) (k : ℤ) :
    (deriv (hillH1PhysicalModeCurve n) 0).val k=
      halfFourierInverseSymbol k*((if k=(n:ℤ) then 1 else 0)+(if k=-(n:ℤ) then 1 else 0)) := by
  rw [(hasDerivAt_hillH1PhysicalModeCurve_zero n).deriv,fderiv_hillH1CanonicalPotential_zero_apply,
    hillH1ModeCLM_apply]
  simp only [map_one]

end NLS.Articles.KdVPseudomeasures
