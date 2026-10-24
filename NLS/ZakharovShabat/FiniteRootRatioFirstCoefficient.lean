import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The first coefficient of a finite root quotient at infinity

Inverting the spectral parameter gives a rational function regular at zero.
Its derivative is the finite sum of denominator roots minus numerator roots.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def finiteRootRatioAtInfinity (s : Finset ℤ) (ξ η : ℤ → ℂ) (t : ℂ) : ℂ :=
  ∏ n ∈ s, (1-t*ξ n)/(1-t*η n)

@[simp] theorem finiteRootRatioAtInfinity_zero (s : Finset ℤ) (ξ η : ℤ → ℂ) :
    finiteRootRatioAtInfinity s ξ η 0 = 1 := by simp [finiteRootRatioAtInfinity]

/-- The first coefficient is the exact finite root-displacement trace. -/
theorem hasDerivAt_finiteRootRatioAtInfinity_zero
    (s : Finset ℤ) (ξ η : ℤ → ℂ) :
    HasDerivAt (finiteRootRatioAtInfinity s ξ η) (∑ n ∈ s, (η n-ξ n)) 0 := by
  have hf (n : ℤ) : HasDerivAt (fun t : ℂ => (1-t*ξ n)/(1-t*η n)) (η n-ξ n) 0 := by
    have hd := ((hasDerivAt_const (0 : ℂ) 1).sub ((hasDerivAt_id (0 : ℂ)).mul_const (ξ n))).div
      ((hasDerivAt_const (0 : ℂ) 1).sub ((hasDerivAt_id (0 : ℂ)).mul_const (η n))) (by simp)
    convert! hd using 1
    simp [sub_eq_add_neg, add_comm]
  change HasDerivAt (fun t : ℂ => ∏ n ∈ s, (1-t*ξ n)/(1-t*η n)) _ 0
  simpa only [zero_mul, sub_zero, div_one, Finset.prod_const_one, one_smul] using
    HasDerivAt.fun_finsetProd (fun n (_ : n ∈ s) => hf n)

/-- The rational germ agrees exactly with the finite root quotient at a nonzero inverse parameter. -/
theorem finiteRootRatioAtInfinity_inv (s : Finset ℤ) (ξ η : ℤ → ℂ)
    (z : ℂ) (hz : z ≠ 0) :
    finiteRootRatioAtInfinity s ξ η z⁻¹ = ∏ n ∈ s, (ξ n-z)/(η n-z) := by
  apply Finset.prod_congr rfl
  intro n _
  rw [show 1-z⁻¹*ξ n = -(ξ n-z)/z by field_simp; ring,
    show 1-z⁻¹*η n = -(η n-z)/z by field_simp; ring]
  rw [div_div_div_cancel_right₀ hz, neg_div_neg_eq]

end NLS.ZakharovShabat
