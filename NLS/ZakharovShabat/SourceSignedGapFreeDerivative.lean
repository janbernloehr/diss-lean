import NLS.ZakharovShabat.SourceSymmetricSignedGaps
import NLS.ZakharovShabat.SourceFreeSpectralDifferentials
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-! # The exact free derivative of the actual signed-gap sequence

The sequence derivative is obtained by continuous coordinate evaluation
of the analytic map. At the free source it is the sum of the reversed
first component and the second component, with no asymptotic remainder.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The full coefficient-valued signed-gap sequence is analytic at zero source. -/
theorem analyticAt_sourceSignedGapSequence_zero :
    AnalyticAt ℂ (sourceSignedGapSequence (p := 2) (by simp) (by norm_num)) 0 := by
  obtain ⟨W,_,hreal,hseq⟩ := exists_sourceSignedGapSequence_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  exact hseq 0 (hreal (by simp [realTypeSourceLocus]))

/-- The exact free derivative retains both original component and frequency conventions. -/
theorem fderiv_sourceSignedGapSequence_zero_apply (h : CoeffPair 2) (n : ℤ) :
    (fderiv ℂ (sourceSignedGapSequence (p := 2) (by simp) (by norm_num)) 0) h n =
      h.fst (-n) + h.snd n := by
  rw [Coeff.fderiv_apply_of_differentiableAt _ _ _ _ analyticAt_sourceSignedGapSequence_zero.differentiableAt]
  have hD := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    (p := 2) (by simp) (by norm_num) .dirichlet 0 (by simp) n).differentiableAt
  have hN := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    (p := 2) (by simp) (by norm_num) .neumann 0 (by simp) n).differentiableAt
  simp only [sourceSignedGapSequence_apply]
  rw [fderiv_fun_sub hD hN]
  simp only [sub_apply,fderiv_canonicalPeriodOneBoundaryRoot_zero,
    BoundaryCondition.extensionSign]
  ring

end NLS.ZakharovShabat
