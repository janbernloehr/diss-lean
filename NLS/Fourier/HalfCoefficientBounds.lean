import NLS.Fourier.FoldedInterval

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal Classical

namespace NLS.Fourier



/-- The normalized half coefficient retains its factor one half in the
unit-interval uniform estimate. -/
theorem norm_halfCoefficient_le_of_bound (f : ℝ → ℂ) (C : ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) (k : ℤ) :
    ‖halfCoefficient f k‖ ≤ C/2 := by
  have hi : ‖∫ x in (0 : ℝ)..1, f x*wave (-k) x‖ ≤ C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun x hx => show ‖f x*wave (-k) x‖ ≤ C from by
        rw [norm_mul,show ‖wave (-k) x‖=1 by simp [wave,Complex.norm_exp],mul_one]
        apply hf x
        have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa using hx
        exact ⟨hx'.1.le,hx'.2⟩)
    simpa using hh
  rw [halfCoefficient,norm_mul]
  norm_num only [norm_div,norm_one,norm_ofNat]
  linarith

end NLS.Fourier
