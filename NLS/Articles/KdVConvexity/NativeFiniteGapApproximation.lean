import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapApproximation

/-! The shared physical recovery uses the SAME already verified original
native finite-gap approximants. These compatibility names retain all source
norms, spectral gap closures and limits without changing prior local helpers. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

abbrev nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :=
  D.nativeFiniteGapApproximation m q N

theorem tendsto_nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    Tendsto (nativeFiniteGapApproximation D m q) atTop (𝓝 q) :=
  D.tendsto_nativeFiniteGapApproximation m q

theorem nativeFiniteGapApproximation_finite_gap (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :
    ∃ S : Finset ℕ+, ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).val
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).property.1
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).property.2 n=0 :=
  D.nativeFiniteGapApproximation_finite_gap m q N

end NLS.Articles.KdVConvexity
