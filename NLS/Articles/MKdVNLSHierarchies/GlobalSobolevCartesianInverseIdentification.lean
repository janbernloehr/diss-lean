import NLS.MKdV.MiuraSobolevActionFiberIdentification

/-! # Global native Sobolev Cartesian inversion and action-fiber identification

These are the actual original coordinates and signed mean, globally
bijective in every native integer H^s class for s>=1. Full Gardner
canonicity and native inverse analyticity are separate obligations.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Any physical L2 preimage of native Cartesian data has the matching
original Sobolev regularity, globally and without an action-fiber premise. -/
theorem physical_Cartesian_inverse_global_Sobolev_regularity (s : ℕ) (a : MiuraRealL2)
    (z : MiuraRealSobolevCartesianTarget s)
    (hz : miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z) :
    ∃ A : MiuraRealSobolevSource s, miuraPhysicalSobolevL2SourceInclusion s A = a :=
  exists_miuraSobolev_representative_of_Cartesian_data s a z hz

/-- Each native order-s datum, s>=1, has one preimage in the entire
physical L2 space, including arbitrary signed mean and closed gaps. -/
theorem physical_Cartesian_global_unique_preimage_nativeSobolev (s : ℕ) (hs : 1 ≤ s)
    (z : MiuraRealSobolevCartesianTarget s) :
    ∃! a : MiuraRealL2, miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z :=
  existsUnique_miuraPhysicalCartesian_preimage_Sobolev s hs z

/-- The literal H^s Cartesian map is a global bijection onto the entire
native positive order-(s+1/2) real pair and real signed mean, for s>=1. -/
theorem physical_Cartesian_global_bijection_nativeSobolev (s : ℕ) (hs : 1 ≤ s) :
    Function.Bijective (miuraPhysicalSobolevCartesianMap s) :=
  miuraPhysicalSobolevCartesianMap_bijective s hs

/-- Physical actions and signed mean determine the entire original NLS
action sequence globally on every original integer H^s domain, s>=1.
Analytic action-variable factorization is a further assertion. -/
theorem physical_NLS_actions_determined_by_mKdV_actions_mean (s : ℕ) (hs : 1 ≤ s)
    (a b : MiuraRealSobolevSource s)
    (hJ : miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s b)) :
    miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val =
      miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val :=
  miuraOriginalNLSActions_eq_of_Sobolev_actionMean_eq s hs a b hJ

end NLS.Articles.MKdVNLSHierarchies
