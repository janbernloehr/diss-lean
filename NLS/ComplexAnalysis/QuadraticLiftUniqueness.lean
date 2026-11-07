import NLS.ComplexAnalysis.QuadraticEnergySheet

/-! Equality of actual quadratic differential pullbacks determines
continuous energy coefficients, also at the removable frequency zero. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem eq_of_quadratic_differential_pullback_eq (P Q : ℂ → ℂ) (hP : Continuous P) (hQ : Continuous Q)
    (c : ℂ) (h : ∀ z : ℂ, 2*z*P (z^2-c) = 2*z*Q (z^2-c)) : P = Q := by
  apply Continuous.ext_on (s := ({-c}:Set ℂ)ᶜ) (dense_compl_singleton (-c)) hP hQ
  intro E hE
  have hsum : E+c ≠ 0 := by
    intro he
    apply hE
    change E = -c
    linear_combination he
  let z := Complex.sqrt (E+c)
  have hsq : z^2 = E+c := complex_sqrt_sq _
  have hzne : z ≠ 0 := by
    intro he
    apply hsum
    rw [he,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hsq
    exact hsq.symm
  have he : z^2-c = E := by rw [hsq]; ring
  have hp := h z
  rw [he] at hp
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hzne) hp

end NLS.ComplexAnalysis
