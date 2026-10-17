import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.OperatorDiagonal

/-! # Compactness from exact diagonal tail rows

A bounded operator with diagonal rows outside a finite head is compact
when its diagonal entries tend to zero. The argument uses a compact
multiplier plus finite output support and includes the exponent infinity.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact diagonal tail rows with vanishing diagonal entries define a compact operator. -/
theorem isCompactOperator_of_tail_diagonal
    (T : Coeff p →L[ℂ] Coeff p) (K : ℕ)
    (hrow : ∀ n : ℤ, K ≤ n.natAbs → ∀ a : Coeff p,
      T a n = a n*T (lp.single p n 1) n)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K' : ℕ, ∀ n : ℤ, K' ≤ n.natAbs →
      ‖T (lp.single p n 1) n‖ < ε) : IsCompactOperator T := by
  let D := multiplierCLM (p := p) (operatorDiagonalSymbol T)
  have hD : IsCompactOperator D := by
    apply isCompactOperator_multiplierCLM
    intro ε hε
    obtain ⟨K',hK'⟩ := htail ε hε
    refine ⟨Finset.Icc (-(K':ℤ)) K',fun n hn => ?_⟩
    exact (hK' n (by simp only [Finset.mem_Icc] at hn; omega)).le
  have he : T-D = (truncateCLM (Finset.Icc (-(K:ℤ)) K)).comp (T-D) := by
    ext a n
    change T a n-D a n = truncate (Finset.Icc (-(K:ℤ)) K) (T a-D a) n
    rw [truncate_apply]
    split_ifs with hn
    · rfl
    · rw [hrow n (by simp only [Finset.mem_Icc] at hn; omega) a]
      change a n*T (lp.single p n 1) n-T (lp.single p n 1) n*a n = 0
      ring
  have hC : IsCompactOperator (T-D) := by
    rw [he]
    exact (isCompactOperator_truncateCLM (p := p) (Finset.Icc (-(K:ℤ)) K)).comp_clm (T-D)
  have h : IsCompactOperator (T-D+D : Coeff p →L[ℂ] Coeff p) := hC.add hD
  simpa only [sub_add_cancel] using h
end NLS.Coeff
