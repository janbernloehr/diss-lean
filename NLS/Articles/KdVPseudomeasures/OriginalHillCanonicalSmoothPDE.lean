import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalCanonicalVector
import NLS.Articles.KdVPseudomeasures.OriginalHillCanonicalSmoothness

/-! The SAME actual canonical flow from every smooth H4 source solves
the LITERAL physical KdV PDE at EVERY real time and EVERY spatial point.
Smoothness is derived from the proved integer-scale restrictions. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerCanonicalKdVFlow_smooth_physical_synthesis
    (q : RealSignedHilbert (signedStepOrder 0 4))
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ))))
    (time : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide)
        (hillIntegerCanonicalKdVFlow 4 q time))) (x : AddCircle (2:ℝ))) := by
  have hinit := hillH1Smooth_mem_hillRealSmoothLocus (hillIntegerSourceOrderInclusion 1 4 (by decide) q) hq
  rw [hillIntegerSourceOrderInclusion_rough] at hinit
  apply contDiff_hillH1_physical_synthesis_of_smooth_locus
  rw [hillIntegerSourceOrderInclusion_rough,hillIntegerCanonicalKdVFlow_inclusion]
  exact hillRoughCanonicalKdVFlow_preserves_smooth_locus _ hinit time

theorem hasDerivAt_hillIntegerCanonicalKdVFlow_physical_PDE
    (q : RealSignedHilbert (signedStepOrder 0 4))
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ))))
    (time x : ℝ) :
    HasDerivAt (fun r : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide)
        (hillIntegerCanonicalKdVFlow 4 q r))) (x : AddCircle (2:ℝ)))
      (classicalKdVVectorField (fun y : ℝ => periodOneSobolevSynthesis
        (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide)
          (hillIntegerCanonicalKdVFlow 4 q time))) (y : AddCircle (2:ℝ))) x) time := by
  let a := hillIntegerCanonicalKdVFlow 4 q time
  let v := hillIntegerCanonicalKdVVector 1 a
  let f := fun y : ℝ => periodOneSobolevSynthesis
    (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) a)) (y : AddCircle (2:ℝ))
  have ha : ContDiff ℝ ∞ f := hillIntegerCanonicalKdVFlow_smooth_physical_synthesis q hq time
  have hgrad := contDiff_classicalKdVGradient f ha
  have hc : Continuous (classicalKdVVectorField f) := by
    rw [← deriv_classicalKdVGradient f ha]
    exact (contDiff_infty_iff_deriv.mp hgrad).2.continuous
  have hp : Function.Periodic (classicalKdVVectorField f) 1 := by
    rw [← deriv_classicalKdVGradient f ha]
    exact NLS.FunctionalAnalysis.periodic_deriv _ 1
      (classicalKdVGradient_periodic f (periodOneSobolevSynthesis_periodic _))
  have hvec : (fun y : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain v) (y : AddCircle (2:ℝ)))=
      classicalKdVVectorField f := by
    apply periodOneSobolevSynthesis_eq_of_coefficients _ _ hc hp
    intro k
    rw [signedOneRealToScalarDomain_apply]
    have h := hillIntegerCanonicalKdVVector_physical_KdV_coefficients a ha k
    change (hillIntegerSourceInclusion 1 v).val.val.val k=_ at h
    rw [hillIntegerSourceInclusion_apply] at h
    exact h
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] ℂ :=
    (((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).comp periodOneSobolevSynthesis).restrictScalars ℝ).comp
      signedOneRealToScalarDomain
  have hd := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp
    (RealSignedHilbert (signedStepOrder 0 1)) ℂ inferInstance inferInstance inferInstance inferInstance
    L _ _ time (hasDerivAt_hillIntegerCanonicalKdVFlow 1 q time)
  change HasDerivAt (fun r : ℝ => periodOneSobolevSynthesis
    (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide)
      (hillIntegerCanonicalKdVFlow 4 q r))) (x : AddCircle (2:ℝ)))
    (periodOneSobolevSynthesis (signedOneRealToScalarDomain v) (x : AddCircle (2:ℝ))) time at hd
  rw [congrFun hvec x] at hd
  exact hd

end NLS.Articles.KdVPseudomeasures
