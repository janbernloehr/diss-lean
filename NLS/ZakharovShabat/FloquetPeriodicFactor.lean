import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring

/-! # Removing a Floquet multiplier by its complex logarithm -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ZakharovShabat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The periodic factor of a curve with a nonzero Floquet multiplier. -/
def floquetPeriodicFactor (μ : ℂ) (F : ℝ → E) (t : ℝ) : E :=
  Complex.exp (-(t : ℂ) * Complex.log μ) • F t

theorem continuous_floquetPeriodicFactor (μ : ℂ) (F : ℝ → E) (hF : Continuous F) :
    Continuous (floquetPeriodicFactor μ F) :=
  (Complex.continuous_exp.comp (Complex.continuous_ofReal.neg.mul_const (Complex.log μ))).smul hF

/-- Multiplication by the inverse exponential removes the entire one-period factor. -/
theorem periodic_floquetPeriodicFactor (μ : ℂ) (hμ : μ ≠ 0) (F : ℝ → E)
    (hF : ∀ t, F (t+1) = μ • F t) : Function.Periodic (floquetPeriodicFactor μ F) 1 := by
  intro t
  simp only [floquetPeriodicFactor,hF,smul_smul,Complex.ofReal_add,Complex.ofReal_one]
  congr 1
  rw [show -(↑t+1)*Complex.log μ = -(t : ℂ)*Complex.log μ-Complex.log μ by ring,
    Complex.exp_sub,Complex.exp_log hμ]
  exact div_mul_cancel₀ _ hμ

/-- Recover the original physical curve from its periodic factor. -/
theorem exp_smul_floquetPeriodicFactor (μ : ℂ) (F : ℝ → E) (t : ℝ) :
    Complex.exp ((t : ℂ)*Complex.log μ) • floquetPeriodicFactor μ F t = F t := by
  rw [floquetPeriodicFactor,smul_smul,← Complex.exp_add,
    show (t : ℂ)*Complex.log μ+ -(t : ℂ)*Complex.log μ = 0 by ring,
    Complex.exp_zero,one_smul]

/-- Every continuous periodic factor is bounded over the entire real line. -/
theorem bounded_floquetPeriodicFactor (μ : ℂ) (hμ : μ ≠ 0) (F : ℝ → E)
    (hcont : Continuous F) (hF : ∀ t, F (t+1) = μ • F t) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, ‖floquetPeriodicFactor μ F t‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := ((periodic_floquetPeriodicFactor μ hμ F hF).isBounded_of_continuous
    one_ne_zero (continuous_floquetPeriodicFactor μ F hcont)).exists_pos_norm_le
  exact ⟨C,hC,fun t => hbound _ ⟨t,rfl⟩⟩

end NLS.ZakharovShabat
