import NLS.MKdV.MiuraCartesianInverseSobolevRegularity
import NLS.MKdV.MiuraRealCartesianGeneralLocalInverse
import NLS.ComplexAnalysis.ClosedRangeChartContinuation

/-! # Every native Sobolev Cartesian datum has a physical preimage

Properness gives closed original-L2 range. Global inverse regularity
places all preimages of native data in H1, where actual L2 local charts
are checked. Connected continuation gives every native datum of order
s+1/2 for each integer s>=1, with a genuine H^s source representative.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPhysicalSobolevL2CartesianInclusion_injective (s : ℕ) :
    Function.Injective (miuraPhysicalSobolevL2CartesianInclusion s) := by
  intro z v hzv
  apply Subtype.ext
  apply miuraPositiveSobolevTarget_ext s
  · intro n hn
    have he := congrArg (fun q : MiuraRealCartesianTarget => miuraPositiveCartesianEval n q.val) hzv
    change miuraPositiveCartesianEval n (miuraPositiveSobolevL2CartesianInclusion s z.val) =
      miuraPositiveCartesianEval n (miuraPositiveSobolevL2CartesianInclusion s v.val) at he
    simpa only [miuraPositiveSobolevL2CartesianInclusion_eval] using he
  · have he := congrArg (fun q : MiuraRealCartesianTarget => q.val.2) hzv
    change (miuraPositiveSobolevL2CartesianInclusion s z.val).2 =
      (miuraPositiveSobolevL2CartesianInclusion s v.val).2 at he
    simpa only [miuraPositiveSobolevL2CartesianInclusion_mean] using he

/-- Every L2 preimage of native order-s data is a point with a checked
open L2 inverse chart, for every integer s>=1. -/
theorem exists_miuraPhysicalCartesian_chart_of_Sobolev_data (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealL2) (z : MiuraRealSobolevCartesianTarget s)
    (hz : miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z) :
    ∃ P : OpenPartialHomeomorph MiuraRealL2 MiuraRealCartesianTarget,
      (P : MiuraRealL2 → MiuraRealCartesianTarget) = miuraPhysicalCartesianMap ∧ a ∈ P.source := by
  obtain ⟨A,hA⟩ := exists_miuraSobolev_representative_of_Cartesian_data s a z hz
  let b := hierarchySobolevToScalarDomain s hs A.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using A.property j
  have he : miuraPhysicalH1L2Point b hb = a := by
    apply Subtype.ext
    ext n
    change scalarInclusion b n = a.val n
    rw [scalarInclusion_apply,hierarchySobolevToScalarDomain_apply,
      ← miuraPhysicalSobolevL2SourceInclusion_apply s A n,hA]
  obtain ⟨P,hP,hbP,_,_⟩ := exists_miuraPhysicalCartesian_analytic_chart_H1 b hb
  exact ⟨P,hP,he ▸ hbP⟩

/-- All native order-s data are attained by the actual original-L2 map. -/
theorem exists_miuraPhysicalCartesian_preimage_Sobolev (s : ℕ) (hs : 1 ≤ s)
    (z : MiuraRealSobolevCartesianTarget s) :
    ∃ a : MiuraRealL2, miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z := by
  have hclosed : IsClosed (range miuraPhysicalCartesianMap) := by
    simpa only [image_univ] using isProperMap_miuraPhysicalCartesianMap.isClosedMap univ isClosed_univ
  apply NLS.ComplexAnalysis.exists_preimage_of_closedRange_of_charts
    miuraPhysicalCartesianMap (miuraPhysicalSobolevL2CartesianInclusion s)
    (miuraPhysicalSobolevL2CartesianInclusion s).continuous hclosed
    (fun v a ha => exists_miuraPhysicalCartesian_chart_of_Sobolev_data s hs a v ha)
    (show ∃ v a, miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s v from
      ⟨0,0,by rw [miuraPhysicalCartesianMap_zero,map_zero]⟩) z

/-- The actual native physical H^s map is onto its entire positive
weighted real Cartesian target and arbitrary signed mean. -/
theorem miuraPhysicalSobolevCartesianMap_surjective (s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (miuraPhysicalSobolevCartesianMap s) := by
  intro z
  obtain ⟨a,ha⟩ := exists_miuraPhysicalCartesian_preimage_Sobolev s hs z
  obtain ⟨A,hA⟩ := exists_miuraSobolev_representative_of_Cartesian_data s a z ha
  refine ⟨A,miuraPhysicalSobolevL2CartesianInclusion_injective s ?_⟩
  rw [miuraPhysicalSobolevCartesianMap_L2,hA,ha]

end NLS.MKdV
