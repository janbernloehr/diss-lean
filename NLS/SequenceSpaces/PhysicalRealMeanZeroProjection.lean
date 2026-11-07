import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! Bounded REAL projection onto the ACTUAL physical mean-zero weighted
space; every already-real raw coefficient and its original norm remain. -/
noncomputable section
namespace NLS

def physicalRealMeanZeroProjection (w : Weight) (hw : ∀ j,w (-j)=w j) :
    WeightedCoeff w 2 →L[ℝ] physicalRealMeanZeroWeightedSubmodule w :=
  (physicalRealMeanZeroWeightedIsometry w hw).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (physicalRealDeletedProjection.comp ((WeightedCoeff.meanZeroWeightedProjectionCLM w).restrictScalars ℝ))

theorem physicalRealMeanZeroProjection_coe (w : Weight) (hw : ∀ j,w (-j)=w j)
    (q : physicalRealMeanZeroWeightedSubmodule w) : physicalRealMeanZeroProjection w hw q.val=q := by
  let a : physicalRealDeletedSubmodule := ⟨WeightedCoeff.meanZeroWeightedProjectionCLM w q.val,
    meanZeroWeightedProjection_real w hw q.val q.property.1⟩
  have ha : physicalRealDeletedProjection (WeightedCoeff.meanZeroWeightedProjectionCLM w q.val)=a :=
    physicalRealDeletedProjection_coe a
  change physicalRealMeanZeroWeightedIsometry w hw
    (physicalRealDeletedProjection (WeightedCoeff.meanZeroWeightedProjectionCLM w q.val))=q
  rw [ha]
  apply Subtype.ext
  exact WeightedCoeff.meanZeroWeightedLift_projection w q.val q.property.2

end NLS
