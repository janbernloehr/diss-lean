import NLS.MKdV.MiuraRealCartesianGeneralLocalInverse
import NLS.ComplexAnalysis.AnalyticEquivalentDerivativeInverse

/-! # Complex Cartesian inverse charts and physical reality at all real H1 points -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The actual complex L2 map has a holomorphic inverse chart at every
physical real original H1 input, with no derivative premise left over. -/
theorem exists_miuraPositiveCartesian_analytic_chart_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ P : OpenPartialHomeomorph (Coeff 2) MiuraPositiveCartesianTarget,
      (P : Coeff 2 → MiuraPositiveCartesianTarget) = miuraPositiveCartesianMap ∧
      scalarInclusion a ∈ P.source ∧ AnalyticOnNhd ℂ miuraPositiveCartesianMap P.source ∧
        AnalyticOnNhd ℂ P.symm P.target := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a))
    (LinearMap.ker_eq_bot.mpr (miuraCartesianJacobian_bijective_H1 a ha).1)
    (LinearMap.range_eq_top.mpr (miuraCartesianJacobian_bijective_H1 a ha).2)
  exact exists_analytic_openPartialHomeomorph_of_fderiv_equiv
    (analyticAt_miuraPositiveCartesianMap _ har) L rfl

/-- Every complex left inverse germ at an original physical real H1
profile preserves the physical real form on nearby real target data. -/
theorem miuraPositiveCartesian_complex_inverse_real_germ_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (g : MiuraPositiveCartesianTarget → Coeff 2)
    (hl : ∀ᶠ b in 𝓝 (scalarInclusion a), g (miuraPositiveCartesianMap b) = b) :
    ∀ᶠ z in 𝓝 (miuraPhysicalCartesianMap (miuraPhysicalH1L2Point a ha)),
      g z.val ∈ Coeff.physicalRealSubmodule 2 := by
  let b := miuraPhysicalH1L2Point a ha
  obtain ⟨P,hP,hb,hA,hG⟩ := exists_miuraPhysicalCartesian_analytic_chart_H1 a ha
  have hPb : miuraPhysicalCartesianMap b ∈ P.target := by
    rw [← hP]
    exact P.map_source hb
  have hc : ContinuousAt P.symm (miuraPhysicalCartesianMap b) := (hG _ hPb).continuousAt
  have hbase : P.symm (miuraPhysicalCartesianMap b) = b := by
    rw [← hP]
    exact P.left_inv hb
  have hr : ∀ᶠ z in 𝓝 (miuraPhysicalCartesianMap b), miuraPhysicalCartesianMap (P.symm z) = z := by
    filter_upwards [P.open_target.mem_nhds hPb] with z hz
    rw [← hP]
    exact P.right_inv hz
  exact inverse_germ_preserves_subspace
    (fun v : MiuraRealL2 => v.val) continuous_subtype_val
    (fun z : MiuraRealCartesianTarget => z.val) miuraPositiveCartesianMap miuraPhysicalCartesianMap
    b g P.symm hc hbase hl hr miuraPhysicalCartesianMap_inclusion
    (fun v => v ∈ Coeff.physicalRealSubmodule 2) (fun v => v.property)

end NLS.MKdV
