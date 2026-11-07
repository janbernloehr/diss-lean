import NLS.SequenceSpaces.SobolevDerivative

/-! A bounded coefficient multiplying an actual squared gap retains
every original Sobolev weight up to twice the gap order. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

theorem weighted_square_majorant_mono
    (t u : ℝ) (hu : u≤2*t) (γ : ℤ → ℂ) (g : Coeff 1)
    (hg : ∀ k, ‖g k‖=Weight.sobolev (2*t) k*‖γ k‖^2) (k : ℤ) :
    Weight.sobolev u k*‖γ k‖^2≤‖g k‖ := by
  rw [hg k]
  exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono hu k) (sq_nonneg _)

theorem weighted_square_factor_bound
    (t u : ℝ) (hu : u≤2*t) (γ β : ℤ → ℂ) (b : Coeff 2) (g : Coeff 1)
    (D : ℝ) (hb : ‖b‖≤D)
    (hg : ∀ k, ‖g k‖=Weight.sobolev (2*t) k*‖γ k‖^2)
    (hβ : ∀ k, β k=(γ k)^2*b k) (k : ℤ) :
    Weight.sobolev u k*‖β k‖≤D*‖g k‖ := by
  rw [hβ k,norm_mul,norm_pow]
  have hbk := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) b k).trans hb
  calc
    _=(Weight.sobolev u k*‖γ k‖^2)*‖b k‖ := by ring
    _≤‖g k‖*D := mul_le_mul (weighted_square_majorant_mono t u hu γ g hg k) hbk
      (norm_nonneg _) (norm_nonneg _)
    _=_ := by ring

end NLS.Coeff
