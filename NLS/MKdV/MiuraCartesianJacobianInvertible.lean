import NLS.MKdV.MiuraCartesianJacobianAnnihilator
import NLS.MKdV.MiuraCartesianFredholm
import NLS.SequenceSpaces.HilbertMatrixTranspose
import NLS.FunctionalAnalysis.CompactDenseRange

/-! # The actual Cartesian Jacobian is invertible at every real H1 profile

The annihilator theorem gives dense range in the full native half-order
target. The checked compact free remainder then supplies bijectivity.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianNormalizedJacobian_denseRange_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    DenseRange (miuraCartesianNormalizedJacobian (scalarInclusion a)) := by
  let A := miuraCartesianNormalizedJacobian (scalarInclusion a)
  apply (Coeff.injective_hilbertMatrixTranspose_iff_denseRange A).mp
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  let L : MiuraPositiveCartesianTarget →L[ℂ] ℂ := (Coeff.dualPairing b).comp miuraCartesianFreeInverse
  have hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0 := by
    apply ContinuousLinearMap.ext
    intro h
    change Coeff.dualPairing b (A h) = 0
    rw [← Coeff.dualPairing_hilbertMatrixTranspose A b h,hb,map_zero]
    rfl
  have hz := miuraCartesianJacobian_annihilator_eq_zero a ha L hL
  ext n
  have h := congrArg (fun Q : MiuraPositiveCartesianTarget →L[ℂ] ℂ =>
    Q (miuraCartesianFreeJacobian (lp.single 2 n 1))) hz
  change Coeff.dualPairing b (miuraCartesianFreeInverse (miuraCartesianFreeJacobian (lp.single 2 n 1))) = 0 at h
  rw [miuraCartesianFreeInverse_jacobian,Coeff.dualPairing_hilbert_single_right] at h
  exact h

theorem miuraCartesianNormalizedJacobian_bijective_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Bijective (miuraCartesianNormalizedJacobian (scalarInclusion a)) := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  apply NLS.CompactSpectrum.bijective_of_denseRange_compact_sub_id
  · exact isCompactOperator_miuraCartesianNormalizedJacobian_sub_id _ har
  · exact miuraCartesianNormalizedJacobian_denseRange_H1 a ha

/-- The full ambient complex L2 derivative into the native positive
half-order Cartesian/mean target is bijective at every real H1 input. -/
theorem miuraCartesianJacobian_bijective_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Function.Bijective (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) := by
  have h := miuraCartesianFreeEquiv.bijective.comp (miuraCartesianNormalizedJacobian_bijective_H1 a ha)
  change Function.Bijective (fun h => miuraCartesianFreeJacobian
    (miuraCartesianFreeInverse (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a) h))) at h
  simpa only [miuraCartesianFreeJacobian_inverse] using h

theorem miuraCartesianJacobian_denseRange_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    DenseRange (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) :=
  (miuraCartesianJacobian_bijective_H1 a ha).2.denseRange

end NLS.MKdV
