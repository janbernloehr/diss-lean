import NLS.ComplexAnalysis.LocalSinhComparison
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! # Local control of the critical phase offset

The hyperbolic sine controls small offsets uniformly over integer imaginary half-periods.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Integer imaginary half-periods change only the sign of the hyperbolic sine. -/
theorem norm_sinh_add_int_pi_I (σ : ℂ) (n : ℤ) :
    ‖sinh (σ+I*(Real.pi:ℂ)*n)‖ = ‖sinh σ‖ := by
  let v := -I*((Real.pi:ℂ)*n)
  have hv : v+(σ+I*(Real.pi:ℂ)*n) = σ := by dsimp [v]; ring
  have hs : sinh v = 0 := by
    dsimp [v]
    rw [neg_mul,sinh_neg,mul_comm I,sinh_mul_I]
    rw [mul_comm (Real.pi:ℂ),Complex.sin_int_mul_pi]
    simp
  have hc : ‖cosh v‖ = 1 := by
    dsimp [v]
    rw [neg_mul,cosh_neg,mul_comm I,cosh_mul_I]
    have he : (Real.pi:ℂ)*n = (((n:ℝ)*Real.pi:ℝ):ℂ) := by push_cast; ring
    rw [he,← ofReal_cos,norm_real,Real.norm_eq_abs,Real.abs_cos_int_mul_pi]
  calc
    _ = ‖cosh v*sinh (σ+I*(Real.pi:ℂ)*n)‖ := by rw [norm_mul,hc,one_mul]
    _ = ‖sinh (v+(σ+I*(Real.pi:ℂ)*n))‖ := by
      rw [sinh_add v (σ+I*(Real.pi:ℂ)*n),hs,zero_mul,zero_add]
    _ = _ := by rw [hv]

/-- A small phase offset is controlled by the hyperbolic sine uniformly
in the integer mode, without choosing an inverse branch. -/
theorem exists_norm_phase_offset_le_sinh :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (σ : ℂ) (n : ℤ),
      ‖σ+I*(Real.pi:ℂ)*n‖ < ε →
      ‖σ+I*(Real.pi:ℂ)*n‖ ≤ 2*‖sinh σ‖ := by
  obtain ⟨ε,hε,h⟩ := exists_norm_sub_le_two_mul_sinh_sub
  refine ⟨ε,hε,?_⟩
  intro σ n hσ
  simpa only [sub_zero,sinh_zero,norm_sinh_add_int_pi_I] using
    h (σ+I*(Real.pi:ℂ)*n) 0 hσ (by simpa only [norm_zero] using hε)

/-- A phase derivative bounded away from zero converts the derivative
of the hyperbolic-cosine model into a bound for the small phase offset. -/
theorem exists_norm_phase_offset_le_trace_derivative :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (σ d : ℂ) (n : ℤ),
      ‖σ+I*(Real.pi:ℂ)*n‖ < ε → (1/2:ℝ) ≤ ‖d‖ →
      ‖σ+I*(Real.pi:ℂ)*n‖ ≤ 2*‖2*sinh σ*d‖ := by
  obtain ⟨ε,hε,h⟩ := exists_norm_phase_offset_le_sinh
  refine ⟨ε,hε,?_⟩
  intro σ d n hσ hd
  have hsmall := h σ n hσ
  rw [norm_mul,norm_mul,norm_ofNat]
  nlinarith [norm_nonneg (sinh σ)]

end NLS.ComplexAnalysis
