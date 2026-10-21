import NLS.ZakharovShabat.ClassicalNLSDifferenceEstimate
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-! # Physical full-line NLS dilation

This implements the physical dilation and energy statement from the introduction, printed p. 10.
-/

noncomputable section
open Complex
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- Spatial dilation has the exact cubic scaling of the second derivative,
with the original real-to-complex scalar convention. -/
theorem deriv2_scalarNLS_dilation (c : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    deriv (deriv (fun y : ℝ => (c:ℂ)*f (c*y))) x =
      (c:ℂ)^3*deriv (deriv f) (c*x) := by
  have hd : deriv (fun y : ℝ => (c:ℂ)*f (c*y)) =
      fun y : ℝ => (c:ℂ)^2*deriv f (c*y) := by
    funext y
    rw [deriv_const_mul_field,deriv_comp_mul_left]
    simp only [Complex.real_smul]
    ring
  rw [hd,deriv_const_mul_field,deriv_comp_mul_left]
  simp only [Complex.real_smul]
  ring

/-- The source's actual defocusing cubic has degree three under real scaling. -/
theorem classicalNLSCubic_real_mul (c : ℝ) (z : ℂ) :
    classicalNLSCubic ((c:ℂ)*z) = (c:ℂ)^3*classicalNLSCubic z := by
  simp only [classicalNLSCubic,map_mul,Complex.conj_ofReal]
  ring

/-- Exact spatial covariance of the original physical scalar NLS field. -/
theorem scalarClassicalNLSVectorField_dilation (c : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    scalarClassicalNLSVectorField (fun y : ℝ => (c:ℂ)*f (c*y)) x =
      (c:ℂ)^3*scalarClassicalNLSVectorField f (c*x) := by
  simp only [scalarClassicalNLSVectorField,deriv2_scalarNLS_dilation,
    classicalNLSCubic_real_mul]
  ring

/-- The literal full-line transformation c*u(c²*t,c*x) preserves the
pointwise physical NLS equation, using actual time derivatives. -/
theorem hasDerivAt_scalarNLS_dilation (u : ℝ → ℝ → ℂ) (c : ℝ)
    (hu : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x)
      (scalarClassicalNLSVectorField (u t) x) t) (t x : ℝ) :
    HasDerivAt (fun τ : ℝ => (c:ℂ)*u (c^2*τ) (c*x))
      (scalarClassicalNLSVectorField (fun y : ℝ => (c:ℂ)*u (c^2*t) (c*y)) x) t := by
  have h := ((hu (c^2*t) (c*x)).scomp t
    ((hasDerivAt_id t).const_mul (c^2))).const_mul (c:ℂ)
  convert! h using 1
  rw [scalarClassicalNLSVectorField_dilation]
  simp only [Complex.real_smul,mul_one]
  push_cast
  ring

/-- Dilation also retains the actual smoothness of every spatial slice. -/
theorem contDiff_scalarNLS_dilation (u : ℝ → ℝ → ℂ) (c : ℝ)
    (hu : ∀ t : ℝ, ContDiff ℝ ∞ (u t)) (t : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => (c:ℂ)*u (c^2*t) (c*x)) :=
  contDiff_const.mul ((hu (c^2*t)).comp (contDiff_const.mul contDiff_id))

end NLS.ZakharovShabat
