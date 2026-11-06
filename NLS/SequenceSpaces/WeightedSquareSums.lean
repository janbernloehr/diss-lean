import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Square sums under a positive lower bound on their weights. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

theorem square_sum_le_of_weight_lower_bound (w g : ℕ → ℝ) (W : ℝ)
    (hW : 0<W) (hw : ∀ k, W ≤ w k)
    (hs : Summable (fun k => (w k)^2*(g k)^2)) :
    Summable (fun k => (g k)^2) ∧
      (∑' k, (g k)^2) ≤ (∑' k, (w k)^2*(g k)^2)/W^2 := by
  have hb (k : ℕ) : (g k)^2 ≤ ((w k)^2*(g k)^2)/W^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hW)).mpr
    have hh : W^2 ≤ (w k)^2 := by nlinarith [hw k]
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (g k))]
  have hgs := Summable.of_nonneg_of_le (fun k => sq_nonneg (g k)) hb (hs.div_const (W^2))
  refine ⟨hgs,?_⟩
  exact (hgs.tsum_le_tsum hb (hs.div_const (W^2))).trans_eq (tsum_div_const)

end NLS.SequenceSpaces
