import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity
import NLS.ZakharovShabat.NormalizedWeightedSourceCompact

/-! # Compact L2 images of real Sobolev balls

Every positive integer Sobolev inclusion is compact, and closures of real ball images remain in the real source locus.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Forgetting a positive integer Sobolev order is compact in the original L2 source norm. -/
theorem isCompactOperator_higherSobolevSourceInclusion (s : ℕ) (hs : 1 ≤ s) :
    IsCompactOperator (higherSobolevSourceInclusion s) := by
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  exact (isCompactOperator_normalizedWeightedSource
    (SpectralWeight.sobolev (s:ℝ) (Nat.cast_nonneg s))
    (SpectralWeight.hasLinearFactor_sobolev (s:ℝ) hs')).comp_clm
      (higherSobolevNormalizedCoordinates s).toContinuousLinearMap

/-- The L2 closure of an original real Sobolev ball is compact and remains real. -/
theorem higherSobolev_real_ball_image_compact (s : ℕ) (hs : 1 ≤ s) (R : ℝ) :
    let K := closure (higherSobolevSourceInclusion s ''
      (closedBall (0 : SobolevSource s) R ∩ (higherSobolevSourceInclusion s ⁻¹' realTypeSourceLocus 2)))
    IsCompact K ∧ K ⊆ realTypeSourceLocus 2 := by
  let X := closedBall (0 : SobolevSource s) R ∩ (higherSobolevSourceInclusion s ⁻¹' realTypeSourceLocus 2)
  have hbounded : Bornology.IsBounded X := isBounded_closedBall.subset inter_subset_left
  refine ⟨IsCompactOperator.isCompact_closure_image_of_bounded
    (f := (higherSobolevSourceInclusion s).toLinearMap)
    (isCompactOperator_higherSobolevSourceInclusion s hs) hbounded,?_⟩
  exact closure_minimal (by rintro _ ⟨a,ha,rfl⟩; exact ha.2) isClosed_realTypeSourceLocus

end NLS.ZakharovShabat
