import NLS.MKdV.MiuraRealH1CartesianLocalInverse
import NLS.MKdV.MiuraRealCartesianInverseRegularity

/-! # Physical real Cartesian inverse charts and regularity on the native Sobolev scale

The actual maps retain every positive Cartesian coefficient and signed
mean. These local results at zero include the literal original real H¹
space. The unique original L² inverse of small native data has the native
Sobolev regularity. No global Gardner-canonical chart is assumed.
-/
noncomputable section
open Set Complex NLS.MKdV
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_real_cartesian_free_jacobian_allSobolev (s : ℕ) :
    ∃ e : MiuraRealSobolevSource s ≃L[ℝ] MiuraRealSobolevCartesianTarget s,
      fderiv ℝ (miuraPhysicalSobolevCartesianMap s) 0 = e.toContinuousLinearMap :=
  ⟨miuraSobolevCartesianRealFreeEquiv s,fderiv_miuraPhysicalSobolevCartesianMap_zero s⟩

theorem physical_real_cartesian_zero_inverse_allSobolev (s : ℕ) :
    ∃ U : Set (MiuraRealSobolevSource s), ∃ V : Set (MiuraRealSobolevCartesianTarget s),
      IsOpen U ∧ IsOpen V ∧ (0 : MiuraRealSobolevSource s) ∈ U ∧ (0 : MiuraRealSobolevCartesianTarget s) ∈ V ∧
      miuraPhysicalSobolevCartesianMap s '' U = V ∧ BijOn (miuraPhysicalSobolevCartesianMap s) U V ∧
      ∃ G : MiuraRealSobolevCartesianTarget s → MiuraRealSobolevSource s,
        AnalyticOnNhd ℝ (miuraPhysicalSobolevCartesianMap s) U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalSobolevCartesianMap s a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalSobolevCartesianMap s (G z) = z) :=
  exists_miuraPhysicalSobolevCartesian_localInverse_at_zero s

theorem physical_real_cartesian_original_H1_zero_inverse :
    ∃ U : Set MiuraRealH1Source, ∃ V : Set (MiuraRealSobolevCartesianTarget 1),
      IsOpen U ∧ IsOpen V ∧ (0 : MiuraRealH1Source) ∈ U ∧ (0 : MiuraRealSobolevCartesianTarget 1) ∈ V ∧
      miuraPhysicalH1CartesianMap '' U = V ∧ BijOn miuraPhysicalH1CartesianMap U V ∧
      ∃ G : MiuraRealSobolevCartesianTarget 1 → MiuraRealH1Source,
        AnalyticOnNhd ℝ miuraPhysicalH1CartesianMap U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalH1CartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalH1CartesianMap (G z) = z) :=
  exists_miuraPhysicalH1Cartesian_localInverse_at_zero

/-- The actual physical L² inverse of small native data is the analytic
native H^s inverse; this quantifies over every possible physical L² preimage. -/
theorem physical_real_cartesian_small_inverse_Sobolev_regularity (s : ℕ) :
    ∃ V : Set (MiuraRealSobolevCartesianTarget s), IsOpen V ∧ (0 : MiuraRealSobolevCartesianTarget s) ∈ V ∧
      ∃ G : MiuraRealSobolevCartesianTarget s → MiuraRealSobolevSource s,
        AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧ ∀ z ∈ V,
          miuraPhysicalSobolevCartesianMap s (G z) = z ∧
          ∀ a : Coeff.physicalRealSubmodule 2,
            miuraPhysicalCartesianMap a = miuraPhysicalSobolevL2CartesianInclusion s z ↔
              a = miuraPhysicalSobolevL2SourceInclusion s (G z) :=
  exists_miuraPhysicalCartesian_small_inverse_Sobolev_regularity s

end NLS.Articles.MKdVNLSHierarchies
