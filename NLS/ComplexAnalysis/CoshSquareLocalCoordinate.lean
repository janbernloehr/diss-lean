import NLS.ComplexAnalysis.CoshSquareCoordinate
import NLS.ComplexAnalysis.BoundaryAnalyticCoordinate

/-! # The squared hyperbolic cosine is a regular coordinate on the positive axis -/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem deriv_coshSquareCoordinate_sq_ne_zero (r : ℝ) (hr : 0 ≤ r) :
    deriv coshSquareCoordinate ((r : ℂ) ^ 2) ≠ 0 := by
  by_cases hr0 : r = 0
  · simpa only [hr0, ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      deriv_coshSquareCoordinate_zero] using (by norm_num : (1 / 2 : ℂ) ≠ 0)
  · have hd := ((analyticOnNhd_coshSquareCoordinate ((r : ℂ) ^ 2) (mem_univ _)).differentiableAt.hasDerivAt).comp
      (r : ℂ) ((hasDerivAt_id (r : ℂ)).pow 2)
    have he : (fun z : ℂ => coshSquareCoordinate (z ^ 2)) = cosh := funext coshSquareCoordinate_sq
    change HasDerivAt (fun z : ℂ => coshSquareCoordinate (z ^ 2)) _ (r : ℂ) at hd
    rw [he] at hd
    have hv := hd.unique (Complex.hasDerivAt_cosh (r : ℂ))
    intro hz
    rw [hz, zero_mul] at hv
    have hs : (sinh (r : ℂ)).re = Real.sinh r := by rw [← ofReal_sinh, ofReal_re]
    have hreal : Real.sinh r = 0 := by rw [← hs, ← hv]; simp
    exact (ne_of_gt (Real.sinh_pos_iff.mpr (lt_of_le_of_ne hr (Ne.symm hr0)))) hreal

end NLS.ComplexAnalysis
