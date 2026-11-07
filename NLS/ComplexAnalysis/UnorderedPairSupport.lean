import Mathlib.Data.Set.Basic

/-! Two unordered pairs with the same support have the same entries up
to interchange, including the singleton support of a collapsed pair. -/
namespace NLS.ComplexAnalysis

theorem eq_or_swap_of_pair_support {A : Type*} (l u a b : A)
    (hl : l=a ∨ l=b) (hu : u=a ∨ u=b) (ha : a=l ∨ a=u) (hb : b=l ∨ b=u) :
    (l=a ∧ u=b) ∨ (l=b ∧ u=a) := by
  rcases hl with hl | hl <;> rcases hu with hu | hu <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst_vars <;> simp_all

end NLS.ComplexAnalysis
