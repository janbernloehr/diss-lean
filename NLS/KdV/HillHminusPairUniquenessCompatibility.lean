import NLS.KdV.HillHminusOnePairUniqueness

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

theorem HillHminusHighGapPair.eq_or_swap_between_radii
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b) :
    (l = a ∧ u = b) ∨ (l = b ∧ u = a) := h.eq_or_swap_of_radii k

end NLS.KdV
