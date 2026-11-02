import NLS.MKdV.MiuraCartesianFreeEquivalence
import NLS.ComplexAnalysis.AnalyticEquivalentDerivativeInverse

/-! # A native analytic inverse chart near the free scalar profile

The actual full Cartesian/mean map has its original derivative identified
with an explicit bounded Fourier equivalence. The Banach analytic inverse
function theorem gives a genuine nonlinear local chart in the original
complex L² and the natural positive-index weighted Hilbert target.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- A full nonlinear analytic inverse on explicit open neighborhoods of
zero in the original source and native positive Cartesian/mean target. -/
theorem exists_miuraPositiveCartesian_localInverse_at_zero :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraPositiveCartesianTarget,
      IsOpen U ∧ IsOpen V ∧ (0 : Coeff 2) ∈ U ∧ (0 : MiuraPositiveCartesianTarget) ∈ V ∧
      miuraPositiveCartesianMap '' U = V ∧ BijOn miuraPositiveCartesianMap U V ∧
      ∃ G : MiuraPositiveCartesianTarget → Coeff 2,
        AnalyticOnNhd ℂ miuraPositiveCartesianMap U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPositiveCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPositiveCartesianMap (G z) = z) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  obtain ⟨P,hP,h0,hA,hG⟩ := exists_analytic_openPartialHomeomorph_of_fderiv_equiv
    (analyticAt_miuraPositiveCartesianMap 0 hzero) miuraCartesianFreeEquiv rfl
  have h0V : (0 : MiuraPositiveCartesianTarget) ∈ P.target := by
    have h := P.map_source h0
    rwa [hP,miuraPositiveCartesianMap_zero] at h
  refine ⟨P.source,P.target,P.open_source,P.open_target,h0,h0V,?_,?_,P.symm,hA,hG,?_,?_,?_⟩
  · rw [← hP]
    exact P.image_source_eq_target
  · rw [← hP]
    exact P.bijOn
  · have h := P.left_inv h0
    rwa [hP,miuraPositiveCartesianMap_zero] at h
  · intro a ha
    rw [← hP]
    exact P.left_inv ha
  · intro z hz
    refine ⟨P.map_target hz,?_⟩
    rw [← hP]
    exact P.right_inv hz

end NLS.MKdV
