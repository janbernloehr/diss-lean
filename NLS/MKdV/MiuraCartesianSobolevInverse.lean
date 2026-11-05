import NLS.MKdV.MiuraCartesianSobolevRange
import NLS.ComplexAnalysis.ProperChartUniqueContinuation

/-! # Global uniqueness for native Sobolev Cartesian data

The full original-L2 fiber of every native order-s datum is a singleton,
for each integer s>=1. This gives a global bijection in the native H^s
spaces, without yet asserting analyticity of its inverse in those norms.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Every native order-s datum, s>=1, has exactly one preimage in the
entire physical real original-L2 space. -/
theorem existsUnique_miuraPhysicalCartesian_preimage_Sobolev (s : ℕ) (hs : 1 ≤ s)
    (z : MiuraRealSobolevCartesianTarget s) :
    ∃! a : MiuraRealL2, miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z := by
  apply NLS.ComplexAnalysis.existsUnique_preimage_of_proper_of_charts
    miuraPhysicalCartesianMap (miuraPhysicalSobolevL2CartesianInclusion s)
    isProperMap_miuraPhysicalCartesianMap (miuraPhysicalSobolevL2CartesianInclusion s).continuous
    (fun v a ha => exists_miuraPhysicalCartesian_chart_of_Sobolev_data s hs a v ha)
    (show ∃ v, ∃! a, miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s v from ?_) z
  refine ⟨0,0,?_,?_⟩
  · simpa only [map_zero] using miuraPhysicalCartesianMap_zero
  · intro a ha
    rw [map_zero] at ha
    exact (miuraPhysicalCartesianMap_eq_zero_iff a).mp ha

/-- Global injectivity in each native integer H^s class, s>=1. -/
theorem miuraPhysicalSobolevCartesianMap_injective (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (miuraPhysicalSobolevCartesianMap s) := by
  intro a b hab
  let z := miuraPhysicalSobolevCartesianMap s a
  obtain ⟨c,_,hu⟩ := existsUnique_miuraPhysicalCartesian_preimage_Sobolev s hs z
  have ha : miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraPhysicalSobolevL2CartesianInclusion s z := (miuraPhysicalSobolevCartesianMap_L2 s a).symm
  have hb : miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s b) =
      miuraPhysicalSobolevL2CartesianInclusion s z :=
    (miuraPhysicalSobolevCartesianMap_L2 s b).symm.trans
      (congrArg (miuraPhysicalSobolevL2CartesianInclusion s) hab.symm)
  exact miuraPhysicalSobolevL2SourceInclusion_injective s ((hu _ ha).trans (hu _ hb).symm)

/-- The actual physical Cartesian map is globally bijective in every
native integer H^s class with s>=1, including arbitrary signed mean and
any pattern of closed gaps. -/
theorem miuraPhysicalSobolevCartesianMap_bijective (s : ℕ) (hs : 1 ≤ s) :
    Function.Bijective (miuraPhysicalSobolevCartesianMap s) :=
  ⟨miuraPhysicalSobolevCartesianMap_injective s hs,miuraPhysicalSobolevCartesianMap_surjective s hs⟩

/-- Equality of actual Cartesian maps implies equality of physical
H^s inputs globally, even when their original NLS action fibers differ. -/
theorem miuraPhysicalCartesian_injective_on_Sobolev (s : ℕ) (hs : 1 ≤ s)
    (a b : MiuraRealSobolevSource s)
    (hab : miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraPhysicalCartesianMap (miuraPhysicalSobolevL2SourceInclusion s b)) : a = b := by
  apply (miuraPhysicalSobolevCartesianMap_bijective s hs).1
  apply miuraPhysicalSobolevL2CartesianInclusion_injective s
  simpa only [miuraPhysicalSobolevCartesianMap_L2] using hab

end NLS.MKdV
