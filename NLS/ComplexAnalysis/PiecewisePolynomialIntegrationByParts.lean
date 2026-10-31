import NLS.ComplexAnalysis.PiecewiseContourPeriod
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Polynomial integration by parts on piecewise smooth circuits

The actual integrals on consecutive C¹ pieces telescope at their vertices.
Only analyticity near the circuit is required, including at its corners.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis.PiecewiseC1Loop

/-- Polynomial integration by parts on every finite piecewise C¹ loop. -/
theorem integral_pow_mul_deriv_eq_neg (Γ : PiecewiseC1Loop)
    (f : ℂ → ℂ) (D : Set ℂ) (hf : AnalyticOnNhd ℂ f D)
    (hΓ : Γ.Inside D) (k : ℕ) :
    Γ.integral (fun z => z^(k+1)*deriv f z) =
      -(k+1 : ℂ)*Γ.integral (fun z => z^k*f z) := by
  have hd (z : ℂ) (hz : z ∈ D) :
      HasDerivAt (fun w => w^(k+1)*f w)
        ((k+1 : ℂ)*z^k*f z+z^(k+1)*deriv f z) z := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,id_eq,Pi.pow_apply,mul_one] using!
      ((hasDerivAt_id z).pow (k+1)).mul (hf z hz).differentiableAt.hasDerivAt
  have hi : ContinuousOn (fun z : ℂ => (k+1 : ℂ)*z^k*f z) D :=
    (continuousOn_const.mul (continuousOn_id.pow k)).mul hf.continuousOn
  have hj : ContinuousOn (fun z : ℂ => z^(k+1)*deriv f z) D :=
    (continuousOn_id.pow (k+1)).mul hf.deriv.continuousOn
  have hz := Γ.integral_eq_zero_of_primitive _ (fun w => w^(k+1)*f w) D
    (hi.add hj) hd hΓ
  change Γ.integral (fun z => (k+1 : ℂ)*z^k*f z+z^(k+1)*deriv f z) = 0 at hz
  rw [Γ.integral_add _ _ hi hj hΓ] at hz
  simp only [mul_assoc,Γ.integral_const_mul] at hz
  exact (eq_neg_of_add_eq_zero_right hz).trans (neg_mul _ _).symm

end NLS.ComplexAnalysis.PiecewiseC1Loop
