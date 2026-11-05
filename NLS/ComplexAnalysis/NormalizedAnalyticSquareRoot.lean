import NLS.ComplexAnalysis.ShiftedSquareRootBounds
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Analytic principal square roots near one

The unit neighborhood avoids the principal cut. The root error is bounded
by the radicand error, uniformly on arbitrary analytic parameter sets.
-/
noncomputable section
set_option autoImplicit false
open Complex Set
namespace NLS.ComplexAnalysis

theorem norm_principalSqrt_sub_one_le (w : ℂ) :
    ‖Complex.sqrt w-1‖ ≤ ‖w-1‖ := by
  simpa using norm_sqrt_sq_add_sub_le (1 : ℂ) (w-1) (by norm_num)

theorem analyticOnNhd_principalSqrt_of_norm_sub_one_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (U : Set E) (hf : AnalyticOnNhd ℂ f U)
    (he : ∀ x ∈ U, ‖f x-1‖ < 1) :
    AnalyticOnNhd ℂ (fun x => Complex.sqrt (f x)) U := by
  intro x hx
  have hneg := neg_le_abs ((f x-1).re)
  have habs := abs_re_le_norm (f x-1)
  have hsmall := he x hx
  have hpos : 0 < (f x).re := by
    simp only [sub_re, one_re] at hneg habs
    linarith
  have hslit : f x ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hpos)
  exact (Complex.differentiableOn_sqrt.analyticAt
    (Complex.isOpen_slitPlane.mem_nhds hslit)).comp (hf x hx)

end NLS.ComplexAnalysis
