import NLS.MKdV.MiuraRealCartesianSmallData

/-! # Physical real Cartesian charts and globally unique small data

These results concern the actual physical Cartesian representatives with
all positive coordinates and signed mean in the native real Hilbert norm.
They give a real local inverse at the free profile and global uniqueness
of preimages for small data. General-profile Gardner canonicity and the
full global Birkhoff identification remain essential obligations.
-/
noncomputable section
open Set Complex NLS.MKdV
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_real_cartesian_free_jacobian_equivalence :
    ∃ e : Coeff.physicalRealSubmodule 2 ≃L[ℝ] MiuraRealCartesianTarget,
      fderiv ℝ miuraPhysicalCartesianMap 0 = e.toContinuousLinearMap :=
  ⟨miuraCartesianRealFreeEquiv,fderiv_miuraPhysicalCartesianMap_zero⟩

theorem physical_real_cartesian_zero_local_inverse :
    ∃ U : Set (Coeff.physicalRealSubmodule 2), ∃ V : Set MiuraRealCartesianTarget,
      IsOpen U ∧ IsOpen V ∧ (0 : Coeff.physicalRealSubmodule 2) ∈ U ∧ (0 : MiuraRealCartesianTarget) ∈ V ∧
      miuraPhysicalCartesianMap '' U = V ∧ BijOn miuraPhysicalCartesianMap U V ∧
      ∃ G : MiuraRealCartesianTarget → Coeff.physicalRealSubmodule 2,
        AnalyticOnNhd ℝ miuraPhysicalCartesianMap U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalCartesianMap (G z) = z) :=
  exists_miuraPhysicalCartesian_localInverse_at_zero

theorem physical_real_cartesian_map_proper : IsProperMap miuraPhysicalCartesianMap :=
  isProperMap_miuraPhysicalCartesianMap

theorem physical_real_cartesian_global_unique_small_data :
    ∃ V : Set MiuraRealCartesianTarget, IsOpen V ∧ (0 : MiuraRealCartesianTarget) ∈ V ∧
      ∀ z ∈ V, ∃! a : Coeff.physicalRealSubmodule 2, miuraPhysicalCartesianMap a = z :=
  exists_miuraPhysicalCartesian_global_unique_small_data

end NLS.Articles.MKdVNLSHierarchies
