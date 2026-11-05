import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith

/-! A differentiable scalar function which is even along a real line has
zero derivative in that direction at the center. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_apply_eq_zero_of_even_line (f : E → ℝ) (z v : E)
    (hf : DifferentiableAt ℝ f z)
    (he : ∀ t : ℝ, f (z+t • v)=f (z+(-t) • v)) :
    (fderiv ℝ f z) v=0 := by
  have hline : HasDerivAt (fun t : ℝ => z+t • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hd : HasDerivAt (fun t : ℝ => f (z+t • v)) ((fderiv ℝ f z) v) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdneg : HasDerivAt (fun t : ℝ => f (z+(-t) • v)) (-((fderiv ℝ f z) v)) 0 := by
    simpa only [Function.comp_def,mul_neg_one] using
      hd.comp_of_eq (0:ℝ) (hasDerivAt_neg (0:ℝ)) (by simp)
  have hfun : (fun t : ℝ => f (z+t • v))=(fun t : ℝ => f (z+(-t) • v)) := funext he
  rw [hfun] at hd
  have hu := hd.unique hdneg
  linarith

end NLS.FunctionalAnalysis
