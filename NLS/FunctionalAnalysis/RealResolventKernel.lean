import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # The bounded nonreal resolvent kernel on the real line -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Complex
namespace NLS.FunctionalAnalysis

/-- A nonreal spectral parameter never equals a real coordinate. -/
theorem nonreal_sub_ofReal_ne_zero (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) : z-(t : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact hz (by simpa using hi)

theorem continuous_realResolventKernel (z : ℂ) (hz : z.im ≠ 0) :
    Continuous (fun t : ℝ => (z-(t : ℂ))⁻¹) :=
  (continuous_const.sub continuous_ofReal).inv₀ (nonreal_sub_ofReal_ne_zero z hz)

/-- The scalar resolvent kernel has the usual uniform inverse-imaginary-part bound. -/
theorem norm_realResolventKernel_le (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    ‖(z-(t : ℂ))⁻¹‖ ≤ 1/|z.im| := by
  have hi : |z.im| ≤ ‖z-(t : ℂ)‖ := by simpa using abs_im_le_norm (z-(t : ℂ))
  simpa only [norm_inv,one_div] using one_div_le_one_div_of_le (abs_pos.mpr hz) hi

/-- The original scalar resolvent kernel is integrable against every finite real measure. -/
theorem integrable_realResolventKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : z.im ≠ 0) : Integrable (fun t : ℝ => (z-(t : ℂ))⁻¹) μ := by
  apply (integrable_const (1/|z.im| : ℝ)).mono'
    (continuous_realResolventKernel z hz).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_realResolventKernel_le z hz)

end NLS.FunctionalAnalysis
