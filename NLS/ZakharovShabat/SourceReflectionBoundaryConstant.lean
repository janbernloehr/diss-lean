import NLS.ZakharovShabat.SourceL2MonodromySymmetries
import NLS.ZakharovShabat.SourceMidpointSpectralData

/-! # The boundary normalization in the nonlocal reflection identity

At a pure-T-even or pure-T-odd original complex L2 source, the monodromy
trace difference and the canonical root both change sign under lambda ->
-lambda. Their quotient therefore has the exact even symmetry required
by the corrected nonlocal primitive-gradient identity.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def sourceDiscriminantBoundaryConstant (φ : CoeffPair 2) (z : ℂ) : ℂ :=
  (l2Monodromy (sourcePhysicalL2 φ) z) 0 0-(l2Monodromy (sourcePhysicalL2 φ) z) 1 1

theorem sourceReciprocalScaling_neg_one (φ : CoeffPair 2) : sourceReciprocalScaling (-1) φ = -φ := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> simp

theorem sourceDiscriminantBoundaryConstant_neg (φ : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantBoundaryConstant (-φ) z = sourceDiscriminantBoundaryConstant φ z := by
  rw [← sourceReciprocalScaling_neg_one φ]
  unfold sourceDiscriminantBoundaryConstant
  rw [l2Monodromy_sourceReciprocalScaling (-1) (by norm_num)]
  simp

theorem sourceDiscriminantBoundaryConstant_midpointReflection (φ : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantBoundaryConstant (sourceMidpointReflection φ) (-z) =
      -sourceDiscriminantBoundaryConstant φ z := by
  unfold sourceDiscriminantBoundaryConstant
  rw [l2Monodromy_sourceMidpointReflection]
  simp

theorem sourceCanonicalRoot_neg_source (φ : CoeffPair 2) (z : ℂ) :
    sourceCanonicalRoot (by simp) (by norm_num) (-φ) z =
      sourceCanonicalRoot (by simp) (by norm_num) φ z := by
  rw [← sourceReciprocalScaling_neg_one φ]
  exact sourceCanonicalRoot_reciprocalScaling (by simp) (by norm_num) (-1) (by norm_num) φ z

theorem source_reflection_boundary_constant_odd (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) (z : ℂ) :
    sourceDiscriminantBoundaryConstant φ (-z) = -sourceDiscriminantBoundaryConstant φ z := by
  have h := sourceDiscriminantBoundaryConstant_midpointReflection φ z
  rcases hT with hT | hT
  · simpa only [hT] using h
  · simpa only [hT,sourceDiscriminantBoundaryConstant_neg] using h

theorem source_reflection_canonical_root_odd (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) (z : ℂ) :
    sourceCanonicalRoot (by simp) (by norm_num) φ (-z) =
      -sourceCanonicalRoot (by simp) (by norm_num) φ z := by
  have h := sourceCanonicalRoot_midpointReflection (by simp) (by norm_num) φ z
  rcases hT with hT | hT
  · simpa only [hT] using h
  · simpa only [hT,sourceCanonicalRoot_neg_source] using h

theorem source_reflection_normalized_boundary_even (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) (z : ℂ) :
    sourceDiscriminantBoundaryConstant φ (-z)/sourceCanonicalRoot (by simp) (by norm_num) φ (-z) =
      sourceDiscriminantBoundaryConstant φ z/sourceCanonicalRoot (by simp) (by norm_num) φ z := by
  rw [source_reflection_boundary_constant_odd φ hT z,source_reflection_canonical_root_odd φ hT z]
  exact neg_div_neg_eq _ _

end NLS.ZakharovShabat
