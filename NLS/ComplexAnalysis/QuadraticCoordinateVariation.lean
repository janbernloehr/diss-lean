import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-! First variation of an analytic quadratic symmetric coordinate. -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_quadratic_coordinate_apply (M G : A → ℂ) (a h : A) (c d : ℂ)
    (hM : DifferentiableAt ℂ M a) (hG : DifferentiableAt ℂ G a) :
    (fderiv ℂ (fun q => M q^2+c*G q+d) a) h =
      2*M a*((fderiv ℂ M a) h)+c*((fderiv ℂ G a) h) := by
  have hd := (((hM.hasFDerivAt.pow 2).add (hG.hasFDerivAt.const_mul c)).add_const d).fderiv
  change fderiv ℂ (fun q => M q^2+c*G q+d) a = _ at hd
  rw [hd]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

end NLS.ComplexAnalysis
