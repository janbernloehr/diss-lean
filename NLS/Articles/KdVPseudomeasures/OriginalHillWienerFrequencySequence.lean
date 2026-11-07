import NLS.Articles.KdVPseudomeasures.OriginalHillL2FrequencySequence
import NLS.Articles.KdVPseudomeasures.OriginalHillWienerPhysicalModels

/-! The actual original KdV frequency correction is bounded and
Banach real analytic on EVERY original physical integer-order Wiener
space, with the SAME entire distribution and exact normalization. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def originalWienerL2Inclusion (N : ℕ) : OriginalWienerPotential N →L[ℝ] HillRealL2BanachSource :=
  (signedIteratedInclusion 0 N).comp
    ((hillWienerSourceHilbertInclusion N).comp (originalWienerSourceCoefficients N).toContinuousLinearMap)

theorem originalWienerL2Inclusion_apply (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    (originalWienerL2Inclusion N q).val.val.val k = q.val.val (NLS.Fourier.SmoothPeriodicTest.mode (-(2*k))) := by
  change (signedIteratedInclusion 0 N (hillWienerSourceHilbertInclusion N
    (originalWienerSourceCoefficients N q))).val.val.val k = _
  rw [signedIteratedInclusion_apply,hillWienerSourceHilbertInclusion_apply]
  exact originalWienerSourceCoefficients_apply N q k

theorem originalWienerL2Inclusion_native (N : ℕ) (q : OriginalWienerPotential N) :
    hillL2SourceInclusion (originalWienerL2Inclusion N q) =
      originalHillRealMeanZeroSource (originalWienerOriginalPotential N q) := by
  rw [originalWienerOriginalPotential_native]
  rfl

def originalWienerKdVRenormalizedFrequencySequence (N : ℕ) (q : OriginalWienerPotential N) : Coeff ⊤ :=
  hillL2KdVRenormalizedFrequencySequence (originalWienerL2Inclusion N q)

theorem analyticAt_originalWienerKdVRenormalizedFrequencySequence (N : ℕ) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalWienerKdVRenormalizedFrequencySequence N) q := by
  have hL := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (OriginalWienerPotential N) inferInstance inferInstance
    HillRealL2BanachSource inferInstance (fourierRealZeroSubmodule_normedSpace _)
    (originalWienerL2Inclusion N) q
  exact (analyticAt_hillL2KdVRenormalizedFrequencySequence _).comp
    (f := fun a : OriginalWienerPotential N => originalWienerL2Inclusion N a) hL

theorem originalWienerKdVRenormalizedFrequencySequence_coefficients
    (N : ℕ) (q : OriginalWienerPotential N) (k : ℤ) :
    originalWienerKdVRenormalizedFrequencySequence N q k = positiveScalarExtension
      (fun n => (hillRoughKdVFrequency n (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-
        (2*(Real.pi:ℂ)*(n:ℤ))^3) k := by
  change hillL2KdVRenormalizedFrequencySequence (originalWienerL2Inclusion N q) k = _
  rw [hillL2KdVRenormalizedFrequencySequence_coefficients,originalWienerL2Inclusion_native]

theorem originalWienerKdVFrequency_remainder_bound (N : ℕ) (q : OriginalWienerPotential N) (n : ℕ+) :
    ‖(hillRoughKdVFrequency n (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-
      (2*(Real.pi:ℂ)*(n:ℤ))^3‖ ≤ ‖originalWienerKdVRenormalizedFrequencySequence N q‖ := by
  have h := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0)
    (originalWienerKdVRenormalizedFrequencySequence N q) (n:ℤ)
  rw [originalWienerKdVRenormalizedFrequencySequence_coefficients,positiveScalarExtension_apply] at h
  exact h

end NLS.Articles.KdVPseudomeasures
