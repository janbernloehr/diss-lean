import NLS.FunctionalAnalysis.NormalOperatorSpectralMeasureNoAtoms
import NLS.ZakharovShabat.L2WholeLineCayleySpectralMeasure
import NLS.ZakharovShabat.L2WholeLineCayleyEigenvectors

/-! # The actual physical Cayley scalar spectral measures have no atoms -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Every actual scalar spectral measure of the physical Cayley transform
vanishes on singletons. This includes all possible band-edge images. -/
instance wholeLineCayleySpectralMeasure_nullSingletonClass (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    NullSingletonClass (wholeLineCayleySpectralMeasure u hu v) :=
  normalOperatorSpectralMeasure_noAtoms _ (wholeLineCayley_isStarNormal u hu)
    (wholeLineCayley_eigenvector_eq_zero u hu) v

/-- Every complex coordinate fiber has zero measure in the actual physical CFC measure. -/
theorem wholeLineCayleySpectralMeasure_coordinate_fiber_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) (ζ : ℂ) :
    wholeLineCayleySpectralMeasure u hu v {x | (x : ℂ) = ζ} = 0 := by
  have hs : ({x : spectrum ℂ (wholeLineCayley u hu) | (x : ℂ) = ζ} : Set _).Subsingleton := by
    intro x hx y hy
    exact Subtype.ext (hx.trans hy.symm)
  exact hs.measure_zero _

/-- The exceptional point of inverse Cayley transport has exactly zero mass. -/
theorem wholeLineCayleySpectralMeasure_one_fiber_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2) :
    wholeLineCayleySpectralMeasure u hu v {x | (x : ℂ) = 1} = 0 :=
  wholeLineCayleySpectralMeasure_coordinate_fiber_zero u hu v 1

/-- All countable exceptional subsets of the actual Cayley spectrum are null. -/
theorem wholeLineCayleySpectralMeasure_countable_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (s : Set (spectrum ℂ (wholeLineCayley u hu))) (hs : s.Countable) :
    wholeLineCayleySpectralMeasure u hu v s = 0 := hs.measure_zero _

end NLS.ZakharovShabat
