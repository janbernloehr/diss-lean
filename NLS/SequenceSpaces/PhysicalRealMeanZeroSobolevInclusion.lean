import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Literal bounded inclusions of original real mean-zero Sobolev spaces -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace NLS

/-- Coefficient-preserving inclusion, with the original real mean-zero norms. -/
def physicalRealMeanZeroSobolevInclusion {s t : ℝ} (h : t≤s) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) →L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev t) :=
  (((WeightedCoeff.sobolevInclusion h).restrictScalars ℝ).comp
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)).subtypeL).codRestrict _ (by
      intro q
      constructor
      · intro j
        change (WeightedCoeff.sobolevInclusion h q.val).val (-j)=
          conj ((WeightedCoeff.sobolevInclusion h q.val).val j)
        simpa only [WeightedCoeff.sobolevInclusion_apply] using q.property.1 j
      · change (WeightedCoeff.sobolevInclusion h q.val).val 0=0
        simpa only [WeightedCoeff.sobolevInclusion_apply] using q.property.2)

@[simp] theorem physicalRealMeanZeroSobolevInclusion_val {s t : ℝ} (h : t≤s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    (physicalRealMeanZeroSobolevInclusion h q).val=WeightedCoeff.sobolevInclusion h q.val := rfl

@[simp] theorem physicalRealMeanZeroSobolevInclusion_coefficient {s t : ℝ} (h : t≤s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (j : ℤ) :
    (physicalRealMeanZeroSobolevInclusion h q).val.val j=q.val.val j :=
  WeightedCoeff.sobolevInclusion_apply h q.val j

end NLS
