import NLS.MKdV.MiuraCartesianLocalInverse

/-! # Properness in the actual positive-index Cartesian target

The closed positive target retains every physical coordinate and signed
mean. Its bounded inclusion recovers the original full encoded map, so
original real L² properness passes to this natural target as well.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraPositiveCartesianInclusion : MiuraPositiveCartesianTarget →L[ℂ] (MiuraL2CartesianTarget × ℂ) :=
  (MiuraPositiveHalf.subtypeL.prodMap MiuraPositiveHalf.subtypeL).prodMap (ContinuousLinearMap.id ℂ ℂ)

/-- Natural positive coordinates lose none of the actual physical map. -/
theorem miuraPositiveCartesianInclusion_map (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    miuraPositiveCartesianInclusion (miuraPositiveCartesianMap a) = miuraL2CartesianMeanMap a := by
  apply Prod.ext
  · apply Prod.ext
    · change (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).1).val =
        (miuraL2CartesianSequence a).1
      apply Subtype.ext
      funext n
      rw [WeightedCoeff.positiveProjection_apply]
      split_ifs with hn
      · rfl
      · have h := congrArg Prod.fst (miuraL2CartesianSequence_nonpositive a ha n hn)
        exact h.symm
    · change (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).2).val =
        (miuraL2CartesianSequence a).2
      apply Subtype.ext
      funext n
      rw [WeightedCoeff.positiveProjection_apply]
      split_ifs with hn
      · rfl
      · have h := congrArg Prod.snd (miuraL2CartesianSequence_nonpositive a ha n hn)
        exact h.symm
  · rfl

def miuraRealPositiveCartesianMap (a : MiuraRealL2) : MiuraPositiveCartesianTarget :=
  miuraPositiveCartesianMap a.val

theorem continuous_miuraRealPositiveCartesianMap : Continuous miuraRealPositiveCartesianMap := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (analyticAt_miuraPositiveCartesianMap a.val a.property).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Compact data in the full natural positive-index Hilbert target and
signed mean have compact preimages in original physical real L². -/
theorem isProperMap_miuraRealPositiveCartesianMap : IsProperMap miuraRealPositiveCartesianMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_miuraRealPositiveCartesianMap,?_⟩
  intro K hK
  have hIK := hK.image miuraPositiveCartesianInclusion.continuous
  have hCK := (isProperMap_iff_isCompact_preimage.mp isProperMap_miuraRealL2CartesianMeanMap).2 hIK
  apply hCK.of_isClosed_subset (hK.isClosed.preimage continuous_miuraRealPositiveCartesianMap)
  intro a ha
  exact ⟨miuraRealPositiveCartesianMap a,ha,miuraPositiveCartesianInclusion_map a.val a.property⟩

end NLS.MKdV
