import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Ring

/-! Equal complex radii differ by one exact unit-speed real rotation,
including radius zero. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem exists_exp_I_mul_eq_of_norm_eq (a b : ℂ) (hab : ‖a‖=‖b‖) :
    ∃ t : ℝ, exp (I*t)*a=b := by
  refine ⟨b.arg-a.arg,?_⟩
  calc
    exp (I*((b.arg-a.arg):ℝ))*a=
        exp (I*((b.arg-a.arg):ℝ))*((‖a‖:ℂ)*exp (a.arg*I)) :=
      congrArg (exp (I*((b.arg-a.arg):ℝ))*·) (norm_mul_exp_arg_mul_I a).symm
    _=(‖a‖:ℂ)*(exp (I*((b.arg-a.arg):ℝ))*exp (a.arg*I)) := by ring
    _=(‖a‖:ℂ)*exp (b.arg*I) := by
      congr 1
      rw [← exp_add]
      congr 1
      push_cast
      ring
    _=b := by rw [hab,norm_mul_exp_arg_mul_I]

end NLS.ComplexAnalysis
