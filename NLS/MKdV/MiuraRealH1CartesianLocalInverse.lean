import NLS.MKdV.MiuraRealSobolevCartesianLocalInverse
import NLS.ComplexAnalysis.RealAnalyticEquivalenceComposition

/-! # The real analytic inverse chart on the literal original physical H¹ domain -/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraRealH1Source := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2

def miuraRealH1SobolevEquiv : MiuraRealH1Source ≃L[ℝ] MiuraRealSobolevSource 1 := by
  let e := complexEquivReal miuraH1SobolevEquiv.toContinuousLinearEquiv
  apply subspaceEquiv e (MiuraRealH1Source) (MiuraRealSobolevSource 1)
  intro a
  change (∀ j, a.val j = conj (a.val (-j))) ↔
    ∀ j, (miuraH1SobolevEquiv a).val j = conj ((miuraH1SobolevEquiv a).val (-j))
  simp only [miuraH1SobolevEquiv_apply]

@[simp] theorem miuraRealH1SobolevEquiv_inclusion (a : MiuraRealH1Source) :
    (miuraRealH1SobolevEquiv a).val = miuraH1SobolevEquiv a.val := rfl

def miuraPhysicalH1CartesianMap (a : MiuraRealH1Source) : MiuraRealSobolevCartesianTarget 1 :=
  miuraPhysicalSobolevCartesianMap 1 (miuraRealH1SobolevEquiv a)

theorem miuraPhysicalH1CartesianMap_inclusion (a : MiuraRealH1Source) :
    (miuraPhysicalH1CartesianMap a).val = miuraH1PositiveCartesianMap a.val :=
  miuraPhysicalSobolevCartesianMap_inclusion 1 (miuraRealH1SobolevEquiv a)

theorem analyticAt_miuraPhysicalH1CartesianMap (a : MiuraRealH1Source) :
    AnalyticAt ℝ miuraPhysicalH1CartesianMap a :=
  (analyticAt_miuraPhysicalSobolevCartesianMap 1 _).comp (miuraRealH1SobolevEquiv.analyticAt a)

def miuraH1CartesianRealFreeEquiv : MiuraRealH1Source ≃L[ℝ] MiuraRealSobolevCartesianTarget 1 :=
  miuraRealH1SobolevEquiv.trans (miuraSobolevCartesianRealFreeEquiv 1)

theorem fderiv_miuraPhysicalH1CartesianMap_zero :
    fderiv ℝ miuraPhysicalH1CartesianMap 0 = miuraH1CartesianRealFreeEquiv.toContinuousLinearMap := by
  exact @fderiv_real_comp_equiv_zero MiuraRealH1Source (MiuraRealSobolevSource 1) (MiuraRealSobolevCartesianTarget 1)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraPhysicalSobolevCartesianMap 1) miuraRealH1SobolevEquiv (miuraSobolevCartesianRealFreeEquiv 1)
    (analyticAt_miuraPhysicalSobolevCartesianMap 1 0) (fderiv_miuraPhysicalSobolevCartesianMap_zero 1)

theorem miuraPhysicalH1CartesianMap_zero : miuraPhysicalH1CartesianMap 0 = 0 := by
  change miuraPhysicalSobolevCartesianMap 1 (miuraRealH1SobolevEquiv 0) = 0
  rw [map_zero,miuraPhysicalSobolevCartesianMap_zero]

/-- The complete real order-three-halves Cartesian pair and signed mean
admit an actual analytic inverse on full original physical H¹ neighborhoods. -/
theorem exists_miuraPhysicalH1Cartesian_localInverse_at_zero :
    ∃ U : Set MiuraRealH1Source, ∃ V : Set (MiuraRealSobolevCartesianTarget 1),
      IsOpen U ∧ IsOpen V ∧ (0 : MiuraRealH1Source) ∈ U ∧ (0 : MiuraRealSobolevCartesianTarget 1) ∈ V ∧
      miuraPhysicalH1CartesianMap '' U = V ∧ BijOn miuraPhysicalH1CartesianMap U V ∧
      ∃ G : MiuraRealSobolevCartesianTarget 1 → MiuraRealH1Source,
        AnalyticOnNhd ℝ miuraPhysicalH1CartesianMap U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalH1CartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalH1CartesianMap (G z) = z) := by
  exact @exists_real_analytic_inverse_neighborhoods_of_fderiv_equiv MiuraRealH1Source (MiuraRealSobolevCartesianTarget 1)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance miuraPhysicalH1CartesianMap
    (analyticAt_miuraPhysicalH1CartesianMap 0) miuraH1CartesianRealFreeEquiv
    fderiv_miuraPhysicalH1CartesianMap_zero miuraPhysicalH1CartesianMap_zero

end NLS.MKdV
