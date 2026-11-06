import NLS.ComplexAnalysis.CoshSquareCoordinate

/-! # The derivative of the entire squared hyperbolic cosine

The chain rule gives an identity without division by the squared
coordinate. It therefore remains valid at zero and is useful for filling
primitive/root quotients at coalescing endpoints.
-/
noncomputable section
set_option autoImplicit false
open Complex Set
namespace NLS.ComplexAnalysis

theorem deriv_coshSquareCoordinate_sq_mul (z : ℂ) :
    deriv coshSquareCoordinate (z^2)*(2*z) = sinh z := by
  have hd := ((analyticOnNhd_coshSquareCoordinate (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_id z).pow 2)
  have he : (fun w : ℂ => coshSquareCoordinate (w^2)) = cosh := funext coshSquareCoordinate_sq
  change HasDerivAt (fun w : ℂ => coshSquareCoordinate (w^2)) _ z at hd
  rw [he] at hd
  simpa only [Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,mul_one,id_eq] using
    hd.unique (Complex.hasDerivAt_cosh z)

theorem sinh_add_I_nat_pi (z : ℂ) (n : ℕ) :
    sinh (z+I*(n:ℂ)*Real.pi) = (-1:ℂ)^n*sinh z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z+I*((n+1:ℕ):ℂ)*Real.pi =
        (z+I*(n:ℂ)*Real.pi)+(Real.pi:ℂ)*I := by push_cast; ring
    rw [he,sinh_add_pi_mul_I,ih,pow_succ]
    ring

end NLS.ComplexAnalysis
