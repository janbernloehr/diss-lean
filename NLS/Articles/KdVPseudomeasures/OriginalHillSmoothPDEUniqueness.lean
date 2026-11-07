import NLS.Articles.KdVPseudomeasures.OriginalHillCanonicalSmoothPDE
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeODEUniqueness

/-! Uniqueness of literal smooth physical KdV trajectories in the actual
H4 source with a genuine H1 time derivative. The PDE is the original
physical coefficient equation, and isospectrality is NOT assumed. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier NLS.LpSequence
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_vector_eq_canonical_of_physical_coefficients
    (q : RealSignedHilbert (signedStepOrder 0 4))
    (hq : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ))))
    (v : RealSignedHilbert (signedStepOrder 0 1))
    (hv : ∀ k, v.val.val.val k=periodOneCoefficient (classicalKdVVectorField
      (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain
        (hillIntegerSourceOrderInclusion 1 4 (by decide) q)) (x : AddCircle (2:ℝ)))) k) :
    v=hillIntegerCanonicalKdVVector 1 q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have hc := hillIntegerCanonicalKdVVector_physical_KdV_coefficients q hq k
  change (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 q)).val.val.val k=_ at hc
  rw [hillIntegerSourceInclusion_apply] at hc
  exact (hv k).trans hc.symm

theorem hasDerivAt_hillNativeCoordinate_of_smooth_PDE
    (γ : ℝ → RealSignedHilbert (signedStepOrder 0 4))
    (v : ℝ → RealSignedHilbert (signedStepOrder 0 1))
    (hs : ∀ t, ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) (γ t))) (x : AddCircle (2:ℝ))))
    (hd : ∀ t, HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r)) (v t) t)
    (hv : ∀ t k, (v t).val.val.val k=periodOneCoefficient (classicalKdVVectorField
      (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain
        (hillIntegerSourceOrderInclusion 1 4 (by decide) (γ t))) (x : AddCircle (2:ℝ)))) k)
    (t : ℝ) (k : ℤ) :
    HasDerivAt (fun r : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 4 (γ r))))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion 4 (γ t))) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 4 (γ t)))) t := by
  have hvc := hillH1_vector_eq_canonical_of_physical_coefficients (γ t) (hs t) (v t) (hv t)
  have hdt := hd t
  rw [hvc] at hdt
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] PeriodOneHminusOne :=
    hillRealMeanZeroInclusion.comp (hillIntegerSourceInclusion 1)
  have hsource := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp
    (RealSignedHilbert (signedStepOrder 0 1)) PeriodOneHminusOne
    inferInstance inferInstance inferInstance inferInstance L _ _ t hdt
  change HasDerivAt (fun r : ℝ => hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1
    (hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r))))
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 (γ t)))) t at hsource
  simp only [hillIntegerSourceOrderInclusion_rough] at hsource
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 4 (γ t))) :=
    (hillIntegerSourceInclusion 4 (γ t)).property
  have hN := ((analyticOnNhd_hillHminusNativeCoordinate k _
    (real_mem_hillHminusActionAngleNativeDomain _ hr)).differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have hc := hN.comp_hasDerivAt t hsource
  change HasDerivAt (fun r : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 4 (γ r))))
    ((fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 4 (γ t))))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillIntegerCanonicalKdVVector 1 (γ t))))) t at hc
  rw [hillIntegerCanonicalKdVVector_rough_native_velocity] at hc
  exact hc

theorem hillSmoothPDECurve_eq_canonicalFlow
    (γ : ℝ → RealSignedHilbert (signedStepOrder 0 4))
    (v : ℝ → RealSignedHilbert (signedStepOrder 0 1))
    (hs : ∀ t, ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis
      (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) (γ t))) (x : AddCircle (2:ℝ))))
    (hd : ∀ t, HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r)) (v t) t)
    (hv : ∀ t k, (v t).val.val.val k=periodOneCoefficient (classicalKdVVectorField
      (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain
        (hillIntegerSourceOrderInclusion 1 4 (by decide) (γ t))) (x : AddCircle (2:ℝ)))) k)
    (t : ℝ) : γ t=hillIntegerCanonicalKdVFlow 4 (γ 0) t := by
  have he := hillRealCurve_eq_canonicalFlow_of_nativeODE (fun r => hillIntegerSourceInclusion 4 (γ r))
    (hasDerivAt_hillNativeCoordinate_of_smooth_PDE γ v hs hd hv) t
  apply hillIntegerSourceInclusion_injective 4
  exact he.trans (hillIntegerCanonicalKdVFlow_inclusion 4 (γ 0) t).symm

end NLS.Articles.KdVPseudomeasures
