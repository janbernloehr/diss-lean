import NLS.ZakharovShabat.ResonantDisplacementMajorant
import NLS.ZakharovShabat.RootDisplacementBudget

/-!
# Summing the common two-root majorant

Summable diagonal, leading, and remainder power tails give an actual
convergent majorant series. Their quantitative estimates combine into the
corrected budget, with the leading Fourier tail kept as an additive term.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The majorant's power series is the exact linear combination of its four convergent parts. -/
theorem resonantDisplacementMajorant_tail_sum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (ha : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0))
    (hl : Summable (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0))
    (hm : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0))
    (hb : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then resonantDisplacementMajorant hp w φ n else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then resonantDisplacementMajorant hp w φ n else 0) =
        2*(2 : ℝ)^(p.toReal-1) *
          ((∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) +
            (2 : ℝ)^(p.toReal-1)/2 *
              ((∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) +
                (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) +
                (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0))) := by
  have hs := (ha.hasSum.add (((hl.hasSum.add hm.hasSum).add hb.hasSum).mul_left ((2 : ℝ)^(p.toReal-1)/2))).mul_left
    (2*(2 : ℝ)^(p.toReal-1))
  have he := hs.congr_fun (g := fun n : ℤ => if N ≤ n.natAbs then resonantDisplacementMajorant hp w φ n else 0) (fun n => by
    by_cases hn : N ≤ n.natAbs <;> simp [resonantDisplacementMajorant, hn])
  exact ⟨he.summable,he.tsum_eq⟩

/-- The component budgets imply the corrected common majorant estimate. -/
theorem resonantDisplacementMajorant_tail_le_budget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (ha : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0))
    (hl : Summable (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0))
    (hm : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0))
    (hb : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0))
    (hA : (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal))
    (hL : (∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) ≤
      ‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal)
    (hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal))) :
    (∑' n : ℤ, if N ≤ n.natAbs then resonantDisplacementMajorant hp w φ n else 0) ≤
      rootDisplacementBudget w φ N := by
  rw [(resonantDisplacementMajorant_tail_sum hp w φ N ha hl hm hb).2]
  have hB2 : ‖φ‖^(2*p.toReal) = (‖φ‖^p.toReal)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hT2 : ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal) =
      (‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have htail := Real.rpow_le_rpow (norm_nonneg _)
    (norm_weightedPairFourierTail_le hp w.toWeight (N/2) φ) (ENNReal.toReal_nonneg (a := p))
  have hc := combine_rootDisplacement_budgets (A := ‖φ‖^p.toReal)
    (T := ‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal)
    (D := (N : ℝ)^(min 1 (p.toReal-1))) (K := (2 : ℝ)^(p.toReal-1))
    (by positivity) (by positivity) htail (by positivity) (by positivity)
    (diagonalSummationConstant_nonneg (p := p)) (offDiagonalSummationConstant_nonneg p)
  apply le_trans _ (by simpa only [← hB2, ← hT2, rootDisplacementBudget, rootDisplacementSummationConstant] using hc)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add hA
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

end NLS.ZakharovShabat
