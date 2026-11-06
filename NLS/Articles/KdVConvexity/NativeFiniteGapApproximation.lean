import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapModeOpening
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedTruncation

/-! # Actual finite-gap approximation in every original native Sobolev norm -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

def nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) :=
  (D.rawIntegerForwardHomeomorph m).symm
    (physicalRealMeanZeroWeightedTruncate N (D.rawIntegerForwardHomeomorph m q))

theorem tendsto_nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    Tendsto (nativeFiniteGapApproximation D m q) atTop (𝓝 q) := by
  have h := (D.rawIntegerForwardHomeomorph m).symm.continuous.continuousAt.tendsto.comp
    (tendsto_physicalRealMeanZeroWeightedTruncate (D.rawIntegerForwardHomeomorph m q))
  simpa only [nativeFiniteGapApproximation,Function.comp_def,Homeomorph.symm_apply_apply] using! h

theorem nativeFiniteGapApproximation_finite_gap (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :
    ∃ S : Finset ℕ+, ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).val
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).property.1
      (nativeHillPhysicalSource m (nativeFiniteGapApproximation D m q N).val
        (nativeFiniteGapApproximation D m q N).property.1).property.2 n = 0 := by
  classical
  let S := (Finset.range N).image (fun j => (⟨j+1,by omega⟩ : ℕ+))
  refine ⟨S,?_⟩
  intro n hn
  apply (D.rawIntegerForwardHomeomorph_zero_iff_closed m _ n).mp
  rw [nativeFiniteGapApproximation,(D.rawIntegerForwardHomeomorph m).apply_symm_apply,
    physicalRealMeanZeroWeightedTruncate_apply]
  have hnN : N < (n : ℕ) := by
    by_contra h
    apply hn
    have hp := n.pos
    exact Finset.mem_image.mpr ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),by
      apply Subtype.ext
      change (n : ℕ)-1+1=(n : ℕ)
      omega⟩
  rw [if_neg (by simp only [Finset.mem_Icc]; omega)]

end NLS.Articles.KdVConvexity
