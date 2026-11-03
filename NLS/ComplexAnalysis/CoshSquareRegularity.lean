import NLS.ComplexAnalysis.CoshSquareLocalCoordinate

/-! # Regularity of the entire squared-cosh coordinate away from its critical values -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ComplexAnalysis

/-- A critical value of the squared-cosh coordinate has square one. -/
theorem coshSquareCoordinate_sq_eq_one_of_deriv_eq_zero (w : ℂ)
    (hd : deriv coshSquareCoordinate w = 0) : coshSquareCoordinate w ^ 2 = 1 := by
  let z := Complex.sqrt w
  have hzw : z ^ 2 = w := complex_sqrt_sq w
  have h := ((analyticOnNhd_coshSquareCoordinate (z ^ 2) (mem_univ _)).differentiableAt.hasDerivAt).comp
    z ((hasDerivAt_id z).pow 2)
  have he : (fun v : ℂ => coshSquareCoordinate (v ^ 2)) = cosh :=
    funext coshSquareCoordinate_sq
  change HasDerivAt (fun v : ℂ => coshSquareCoordinate (v ^ 2)) _ z at h
  rw [he] at h
  have hv := h.unique (Complex.hasDerivAt_cosh z)
  rw [hzw,hd,zero_mul] at hv
  have hc := cosh_sq_sub_sinh_sq z
  rw [← hv,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] at hc
  rw [← hzw,coshSquareCoordinate_sq]
  exact hc

theorem deriv_coshSquareCoordinate_ne_zero_of_value_sq_ne_one (w : ℂ)
    (h : coshSquareCoordinate w ^ 2 ≠ 1) : deriv coshSquareCoordinate w ≠ 0 := by
  intro hd
  exact h (coshSquareCoordinate_sq_eq_one_of_deriv_eq_zero w hd)

end NLS.ComplexAnalysis
