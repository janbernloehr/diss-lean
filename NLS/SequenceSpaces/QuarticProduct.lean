import NLS.SequenceSpaces.DoublingProduct

/-!
# The `ℓ4 × ℓ4 → ℓ2` product

Hölder gives the product estimate used with the discrete Cotlar identity.
The square product has exactly the square of the original `ℓ4` norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple 4 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- Pointwise multiplication of two quartic-summable sequences. -/
def quarticProduct : Coeff 4 →L[ℂ] Coeff 4 →L[ℂ] Coeff 2 :=
  doublingProduct (p := 2)

@[simp] theorem quarticProduct_apply (a b : Coeff 4) (n : ℤ) :
    quarticProduct a b n = a n * b n := rfl

theorem norm_quarticProduct_le (a b : Coeff 4) : ‖quarticProduct a b‖ ≤ ‖a‖ * ‖b‖ :=
  norm_doublingProduct_le a b

/-- The square product converts the quartic norm to the Hilbert norm without loss. -/
theorem norm_quarticProduct_self (a : Coeff 4) : ‖quarticProduct a a‖ = ‖a‖ ^ 2 :=
  norm_doublingProduct_self (by norm_num) (by norm_num) a

end NLS.Coeff
