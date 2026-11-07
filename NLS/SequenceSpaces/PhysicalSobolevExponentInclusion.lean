import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedRelift

/-! # Coefficient-preserving inclusions of the original physical Fourier spaces -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

def physicalSobolevExponentInclusion {s t : ℝ} {p r : ℝ≥0∞}
    [Fact (1≤p)] [Fact (1≤r)] (hst : t≤s) (hpr : p≤r) :
    physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p →L[ℝ]
      physicalRealMeanZeroWeightedExponent (Weight.sobolev t) r :=
  (((WeightedCoeff.sobolevExponentInclusion hst hpr).restrictScalars ℝ).comp
    (physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p).subtypeL).codRestrict
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev t) r) (by
        intro a
        constructor
        · intro n
          change (WeightedCoeff.sobolevExponentInclusion hst hpr a.val).val (-n)=
            (starRingEnd ℂ) ((WeightedCoeff.sobolevExponentInclusion hst hpr a.val).val n)
          simpa only [WeightedCoeff.sobolevExponentInclusion_apply] using a.property.1 n
        · change (WeightedCoeff.sobolevExponentInclusion hst hpr a.val).val 0=0
          simpa only [WeightedCoeff.sobolevExponentInclusion_apply] using a.property.2)


@[simp] theorem physicalSobolevExponentInclusion_apply {s t : ℝ} {p r : ℝ≥0∞}
    [Fact (1≤p)] [Fact (1≤r)] (hst : t≤s) (hpr : p≤r)
    (a : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) (n : ℤ) :
    (physicalSobolevExponentInclusion hst hpr a).val.val n=a.val.val n :=
  WeightedCoeff.sobolevExponentInclusion_apply hst hpr a.val n

theorem exists_physicalWeightedRelift (w v : Weight)
    (q : physicalRealMeanZeroWeightedExponent w 2)
    (hm : Memℓp (fun j => (v j : ℂ)*q.val.val j) 2) :
    ∃ a : physicalRealMeanZeroWeightedExponent v 2, ∀ j : ℤ, q.val.val j=a.val.val j :=
  ⟨physicalRealMeanZeroWeightedRelift q hm,
    fun j => (physicalRealMeanZeroWeightedRelift_coefficient q hm j).symm⟩

end NLS
