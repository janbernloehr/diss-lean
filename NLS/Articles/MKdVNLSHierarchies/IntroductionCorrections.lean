import NLS.ZakharovShabat.ClassicalNLSFocusingReduction
import NLS.ComplexAnalysis.CartesianPlaneRotation

/-! # Corrected scalar reductions and Cartesian equations in the introduction

The actual NLS energy fixes the cubic coefficient two, omitted in both
scalar displays on page 2. The second mKdV Cartesian equation uses the
first coordinate, as required by the actual clockwise rotation.
-/
noncomputable section
open Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.Articles.MKdVNLSHierarchies

theorem introduction_defocusing_NLS_reduction (a : ℝ → ℂ) (x : ℝ) :
    I*(classicalNLSVectorField a (fun y => star (a y))).1 x =
      -deriv (deriv a) x+2*(‖a x‖^2 : ℝ)*a x :=
  classicalNLSVectorField_scalar a x

theorem introduction_focusing_NLS_reduction (a : ℝ → ℂ) (x : ℝ) :
    (classicalNLSVectorField (fun y => I*a y) (fun y => I*star (a y))).1 x =
      -deriv (deriv a) x-2*(‖a x‖^2 : ℝ)*a x :=
  classicalNLSVectorField_focusing a x

theorem introduction_defocusing_cubic_coefficient_one_false :
    I*(classicalNLSVectorField (fun _ : ℝ => (1:ℂ)) (fun _ => (1:ℂ))).1 0 ≠ 1 := by
  rw [classicalNLSVectorField_defocusing_constant_one]
  norm_num

theorem introduction_focusing_cubic_coefficient_one_false :
    (classicalNLSVectorField (fun _ : ℝ => I) (fun _ => I)).1 0 ≠ -1 := by
  rw [classicalNLSVectorField_focusing_constant_one]
  norm_num

theorem introduction_mKdV_cartesian_equations (η : ℝ) (z : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => cartesianPlaneRotation (η*r) z)
      ((η:ℂ)*(cartesianPlaneRotation (η*t) z).2,
        -(η:ℂ)*(cartesianPlaneRotation (η*t) z).1) t := by
  have h := (hasDerivAt_cartesianPlaneRotation z (η*t)).scomp t ((hasDerivAt_id t).const_mul η)
  convert! h using 1
  simp

theorem introduction_mKdV_action_preserved (η t : ℝ) (z : ℂ × ℂ) :
    ((cartesianPlaneRotation (η*t) z).1^2+(cartesianPlaneRotation (η*t) z).2^2)/2 =
      (z.1^2+z.2^2)/2 := by rw [cartesianPlaneRotation_radius]

theorem introduction_printed_cartesian_second_equation_false :
    deriv (fun t : ℝ => (cartesianPlaneRotation t (1,2)).2) 0 ≠ -(2:ℂ) := by
  have h := (hasDerivAt_cartesianPlaneRotation ((1,2):ℂ × ℂ) 0).snd
  have hd := HasFDerivAt.hasDerivAt h
  rw [hd.deriv,cartesianPlaneRotation_zero]
  norm_num

end NLS.Articles.MKdVNLSHierarchies
