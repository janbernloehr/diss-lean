import NLS.FunctionalAnalysis.RealPoissonKernel
import NLS.FunctionalAnalysis.IntervalMeasureDomination
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! # Uniform Poisson bounds imply absolute continuity -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace NLS.FunctionalAnalysis

/-- A uniform bound on the unnormalized Poisson transform gives a quantitative
Lebesgue domination bound for the original finite measure. -/
theorem measure_le_volume_of_poisson_bound (μ : Measure ℝ) [IsFiniteMeasure μ] (C : ℝ≥0)
    (h : ∀ x ε : ℝ, 0 < ε → (∫ t, realPoissonKernel x ε t ∂μ) ≤ C) :
    μ ≤ C • (volume : Measure ℝ) := by
  apply measure_le_smul_volume_of_real_Icc
  intro a b hab
  let x := (a+b)/2
  let ε := (b-a)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hxleft : x-ε = a := by dsimp [x,ε]; ring
  have hxright : x+ε = b := by dsimp [x,ε]; ring
  have hi := measureReal_Icc_le_of_poisson_bound μ x ε C hε (h x ε hε)
  rw [hxleft,hxright] at hi
  calc
    μ.real (Icc a b) ≤ 2*ε*C := hi
    _ = (C : ℝ)*(b-a) := by dsimp [ε]; ring

/-- The bound is a sufficient condition for absolute continuity, not a
replacement for proving it for a particular operator. -/
theorem absolutelyContinuous_volume_of_poisson_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C : ℝ≥0) (h : ∀ x ε : ℝ, 0 < ε → (∫ t, realPoissonKernel x ε t ∂μ) ≤ C) :
    μ ≪ (volume : Measure ℝ) := by
  exact (measure_le_volume_of_poisson_bound μ C h).absolutelyContinuous.trans
    (Measure.AbsolutelyContinuous.rfl.smul_left C)

end NLS.FunctionalAnalysis
