import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral
import NLS.SequenceSpaces.TwoSymmetricInfinityModes

/-! Exact original distribution realizing a finite symmetric potential.
The physical mean, reality and period-one conditions are verified on its
original smooth-test actions. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

def sourceTwoModeOriginalPotential (w : SpectralWeight) (r : ℝ) (m : ℤ) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ :=
  (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).symm
    (twoSymmetricInfinityModes (w.negativeSobolev r) m)

theorem sourceTwoModeOriginalPotential_coefficients (w : SpectralWeight) (r : ℝ) (m : ℤ) :
    sourceWeightedEndpointCoefficients w r (sourceTwoModeOriginalPotential w r m) =
      twoSymmetricInfinityModes (w.negativeSobolev r) m :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem sourceTwoModeOriginalPotential_apply (w : SpectralWeight) (r : ℝ) (m k : ℤ) :
    (sourceTwoModeOriginalPotential w r m).val (mode k) =
      (if -k=m then 1 else 0)+(if -k=-m then 1 else 0) := by
  have h := congrArg (fun a : WeightedCoeff (w.negativeSobolev r) ⊤ => a.val (-k))
    (sourceTwoModeOriginalPotential_coefficients w r m)
  simpa only [sourceWeightedEndpointCoefficients_apply,neg_neg,twoSymmetricInfinityModes_apply] using h

theorem sourceTwoModeOriginalPotential_physical (w : SpectralWeight) (r : ℝ) (j : ℤ)
    (hj : j ≠ 0) : (sourceTwoModeOriginalPotential w r (2*j)).val.IsRealMeanZeroPeriodOne := by
  rw [Distribution.isRealMeanZeroPeriodOne_iff_coefficients]
  refine ⟨?_,?_,?_⟩
  · rw [sourceTwoModeOriginalPotential_apply]
    simp only [neg_zero,if_neg (show (0:ℤ)≠2*j by omega),
      if_neg (show (0:ℤ)≠ -(2*j) by omega),zero_add]
  · intro k
    simp only [sourceTwoModeOriginalPotential_apply,neg_neg]
    have h₁ : -k=2*j ↔ k= -(2*j) := by omega
    have h₂ : -k= -(2*j) ↔ k=2*j := by omega
    simp only [h₁,h₂]
    split_ifs <;> norm_num
  · intro k
    rw [sourceTwoModeOriginalPotential_apply]
    simp only [neg_neg,if_neg (show 2*k+1≠2*j by omega),
      if_neg (show 2*k+1≠ -(2*j) by omega),zero_add]

end NLS.Articles.KdVPseudomeasures
