import NLS.KdV.ClassicalBranchPrimitive

noncomputable section
open Set Complex
namespace NLS.KdV
theorem deriv_squaredCosh_sq_mul (z : ℂ) :
    deriv squaredCosh (z^2)*(2*z) = sinh z := by
  have hd := ((analyticOnNhd_squaredCosh (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_id z).pow 2)
  change HasDerivAt (fun w : ℂ => squaredCosh (w^2)) _ z at hd
  have he : (fun w : ℂ => squaredCosh (w^2)) = cosh := funext squaredCosh_sq
  rw [he] at hd
  simpa using hd.unique (Complex.hasDerivAt_cosh z)


end NLS.KdV
