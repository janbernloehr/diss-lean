import NLS.SequenceSpaces.SignedHilbertPairs
import NLS.SequenceSpaces.QuadraticActionsExponent

/-! Exact products of opposite signed pair coordinates. The identity
holds on the complex space and retains the original sqrt(2) factor. -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem signedPairToDeleted_product (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2) (k : ℤ) :
    (signedPairToDeleted e z).val (positiveIndexInjection e k)*
      (signedPairToDeleted e z).val (-positiveIndexInjection e k)=
        quadraticActionsExponent (q := 1) z k := by
  rw [signedPairToDeleted_positive,signedPairToDeleted_negative,quadraticActionsExponent_apply,
    div_mul_div_comm]
  have hs : (Real.sqrt 2 : ℂ)*(Real.sqrt 2 : ℂ)=2 := by
    rw [←Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num : (0 : ℝ)≤2)]
    rfl
  rw [hs]
  congr 1
  calc
    _=z.1 k^2-I^2*z.2 k^2 := by ring
    _=_ := by rw [I_sq];ring

end NLS
