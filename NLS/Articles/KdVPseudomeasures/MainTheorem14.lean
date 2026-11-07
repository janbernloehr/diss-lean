import NLS.Articles.KdVPseudomeasures.OriginalHillInverseActionCoercivity
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeBoundedLimits
import NLS.FunctionalAnalysis.BoundedPreimagesOfNormControl

/-! The complete original Theorem 1.4. Actual inverse-action coercivity
bounds compact target preimages in the original source norm; the verified
native compactness and literal Wiener topology transfer finish the proof. -/
noncomputable section
open Set Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem bounded_hillRealSignedMap_preimage_of_isCompact
    (K : Set HillRealSignedTarget) (hK : IsCompact K) :
    Bornology.IsBounded (hillRealSignedMap ⁻¹' K) := by
  apply NLS.FunctionalAnalysis.bounded_preimage_of_continuous_norm_control
    hillRealSignedMap (fun t => hillMiuraNormBoundConstant*
      (Real.sqrt (t^2/(2*Real.pi))+t^2/(2*Real.pi))) _ _ K hK
  · exact continuous_const.mul
      ((Real.continuous_sqrt.comp ((continuous_id.pow 2).div_const _)).add
        ((continuous_id.pow 2).div_const _))
  · intro q
    simpa only [hillNativeInverseActionMass_eq_norm_sq] using! norm_hillReal_le_inverseActionMass q

theorem isProperMap_hillRealSignedMap : IsProperMap hillRealSignedMap :=
  isProperMap_hillRealSignedMap_iff_bounded_compact_preimages.mpr
    bounded_hillRealSignedMap_preimage_of_isCompact

theorem surjective_hillRealSignedMap : Function.Surjective hillRealSignedMap :=
  (hillPhysicalNative_bijective_iff_isClosedMap.mpr isProperMap_hillRealSignedMap.isClosedMap).2

/-- All clauses of the original source statement, including every bounded
endpoint subset with its literal physical Wiener weak-star topologies. -/
theorem sourceTheorem1_4 : sourceTheorem1_4Statement :=
  sourceTheorem1_4_of_bounded_compact_native_preimages
    bounded_hillRealSignedMap_preimage_of_isCompact

end NLS.Articles.KdVPseudomeasures
