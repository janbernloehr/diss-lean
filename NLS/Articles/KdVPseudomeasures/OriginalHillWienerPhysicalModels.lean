import NLS.Articles.KdVPseudomeasures.OriginalHillL2OneSmoothing
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.Fourier.RealPeriodOneSobolevCoefficients

/-! The original physical Wiener source and the literal ordinary
Sobolev-weighted ell-one target. All Banach equivalences preserve every
coefficient and every original smooth-test distribution value. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

abbrev OriginalWienerPotential (N : ℕ) := realPeriodOneSobolevSubmodule (N:ℝ) 1
abbrev OriginalWienerTarget (N : ℕ) :=
  fourierRealZeroSubmodule (Weight.sobolev (signedStepOrder (1/2) N)) 1

private def sourceSignedOrderEquiv (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (N:ℝ)) 1 ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 :=
  fourierRealWeightEquiv _ _ (Weight.signedSobolev_neg _) (Weight.signedSobolev_neg _) 1 1
    zero_le_one zero_le_one
    (by intro k; rw [hillIntegerSobolev_source_order,one_mul])
    (by intro k; rw [hillIntegerSobolev_source_order,one_mul])

def originalWienerSourceCoefficients (N : ℕ) : OriginalWienerPotential N ≃L[ℝ]
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 :=
  (realPeriodOneSignedSobolevEquiv (N:ℝ) 1 (by positivity)).trans (sourceSignedOrderEquiv N)

theorem originalWienerSourceCoefficients_apply (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    (originalWienerSourceCoefficients N q).val.val.val k = q.val.val (mode (-(2*k))) := by
  change (sourceSignedOrderEquiv N (realPeriodOneSignedSobolevEquiv (N:ℝ) 1 (by positivity) q)).val.val.val k = _
  rw [sourceSignedOrderEquiv,fourierRealWeightEquiv_apply,realPeriodOneSignedSobolevEquiv_apply]

def originalWienerTargetCoefficients (N : ℕ) : OriginalWienerTarget N ≃L[ℝ]
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1 :=
  sobolevSignedRealEquiv _ (by rw [hillIntegerSobolev_target_order]; positivity)

theorem originalWienerTargetCoefficients_symm_apply (N : ℕ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1) (k : ℤ) :
    ((originalWienerTargetCoefficients N).symm a).val.val.val k = a.val.val.val k :=
  sobolevSignedRealEquiv_symm_apply _ _ a k

theorem originalWienerTarget_order (N : ℕ) : signedStepOrder (1/2) N = (N:ℝ)+1/2 :=
  hillIntegerSobolev_target_order N

def originalWienerNativeSource (N : ℕ) : OriginalWienerPotential N →L[ℝ] HillRealMeanZeroSource :=
  (hillWienerSourceInclusion N).comp (originalWienerSourceCoefficients N).toContinuousLinearMap

theorem originalWienerNativeSource_apply (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    (originalWienerNativeSource N q).val.val.val k = q.val.val (mode (-(2*k))) := by
  rw [originalWienerNativeSource,ContinuousLinearMap.comp_apply,hillWienerSourceInclusion_apply]
  exact originalWienerSourceCoefficients_apply N q k

def originalWienerOriginalPotential (N : ℕ) (q : OriginalWienerPotential N) : OriginalHminusOnePotential :=
  originalHillPotentialOfRealSource (originalWienerNativeSource N q)

theorem originalWienerOriginalPotential_same_distribution (N : ℕ) (q : OriginalWienerPotential N) :
    (originalWienerOriginalPotential N q).val.val = q.val.val := by
  apply Distribution.ext_coefficients
  intro k
  change (periodOneOriginal (hillRealMeanZeroInclusion (originalWienerNativeSource N q))).val (mode (-k)) = _
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,periodOneOriginal_even]
    exact originalWienerNativeSource_apply N q (k/2)
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,periodOneOriginal_odd,realPeriodOneSobolev_odd_coefficient]

theorem originalWienerOriginalPotential_native (N : ℕ) (q : OriginalWienerPotential N) :
    originalHillRealMeanZeroSource (originalWienerOriginalPotential N q) = originalWienerNativeSource N q :=
  originalHillRealMeanZeroSource_ofRealSource _

end NLS.Articles.KdVPseudomeasures
