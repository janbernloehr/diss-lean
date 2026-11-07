import NLS.KdV.HillDiscriminantGardnerGradient
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! The actual source cotangent of the Hill discriminant is jointly
entire in energy and the full H-minus-one source. In particular its
energy-contour integrals are genuine integrals in the full source dual. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

def hillHminusDiscriminantCotangent (μ : ℂ) (q : PeriodOneHminusOne) :
    PeriodOneHminusOne →L[ℂ] ℂ :=
  fderiv ℂ (fun p => hillHminusDiscriminant p μ) q

theorem hillHminusDiscriminantCotangent_eq_joint (μ : ℂ) (q : PeriodOneHminusOne) :
    hillHminusDiscriminantCotangent μ q=
      (fderiv ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1) (μ,q)).comp
        (ContinuousLinearMap.inr ℂ ℂ PeriodOneHminusOne) :=
  NLS.ComplexAnalysis.fderiv_source_section_eq_joint _ μ q
    (analyticOnNhd_hillHminusDiscriminant_joint (μ,q) (mem_univ _)).differentiableAt

theorem analyticOnNhd_hillHminusDiscriminantCotangent_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminantCotangent t.1 t.2) univ := by
  intro t _
  let J : ((ℂ × PeriodOneHminusOne) →L[ℂ] ℂ) →L[ℂ] (PeriodOneHminusOne →L[ℂ] ℂ) :=
    (ContinuousLinearMap.inr ℂ ℂ PeriodOneHminusOne).precomp ℂ
  have h := (J.analyticAt _).comp (analyticOnNhd_hillHminusDiscriminant_joint.fderiv t (mem_univ _))
  convert h using 1
  funext p
  exact hillHminusDiscriminantCotangent_eq_joint p.1 p.2

theorem analyticOnNhd_hillHminusDiscriminantCotangent_energy (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (fun μ => hillHminusDiscriminantCotangent μ q) univ := by
  intro μ _
  exact (analyticOnNhd_hillHminusDiscriminantCotangent_joint (μ,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem circleIntegrable_hillHminusDiscriminantCotangent
    (q : PeriodOneHminusOne) (c : ℂ) (R : ℝ) :
    CircleIntegrable (fun μ => hillHminusDiscriminantCotangent μ q) c R :=
  (analyticOnNhd_hillHminusDiscriminantCotangent_energy q).continuous.continuousOn.circleIntegrable'

end NLS.KdV
