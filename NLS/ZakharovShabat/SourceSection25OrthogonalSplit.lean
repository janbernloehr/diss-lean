import NLS.ZakharovShabat.WeightedResonance
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Orthogonality of the actual weighted Fourier projections in Section 25 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Complementary Fourier masks are orthogonal in the exact weighted Hilbert norm. -/
theorem weightedMask_inner_complement (w : Weight) (s : ℤ → Prop) [DecidablePred s]
    (f g : WeightedCoeff w 2) :
    inner ℂ (WeightedCoeff.weightIsometry w 2 (weightedMask w s f))
      (WeightedCoeff.weightIsometry w 2 (weightedMask w (fun k => ¬s k) g)) = 0 := by
  rw [lp.inner_eq_tsum]
  apply (tsum_congr (fun k => ?_)).trans tsum_zero
  change inner ℂ ((w k : ℂ)*(weightedMask w s f).val k)
    ((w k : ℂ)*(weightedMask w (fun k => ¬s k) g).val k) = 0
  by_cases hk : s k <;> simp [weightedMask_apply,hk]

/-- The printed P/Q splitting is orthogonal for arbitrary complex weighted pairs. -/
theorem weightedResonantSplit_inner_eq_zero (w : Weight) (n : ℤ)
    (f g : WeightedCoeffPair w 2) :
    inner ℂ (WeightedCoeff.weightIsometry w 2 (resonantProjection w n f).fst)
        (WeightedCoeff.weightIsometry w 2 (complementaryProjection w n g).fst) +
      inner ℂ (WeightedCoeff.weightIsometry w 2 (resonantProjection w n f).snd)
        (WeightedCoeff.weightIsometry w 2 (complementaryProjection w n g).snd) = 0 := by
  change inner ℂ (WeightedCoeff.weightIsometry w 2 (weightedMask w (· = -n) f.fst))
      (WeightedCoeff.weightIsometry w 2 (weightedMask w (· ≠ -n) g.fst)) +
    inner ℂ (WeightedCoeff.weightIsometry w 2 (weightedMask w (· = n) f.snd))
      (WeightedCoeff.weightIsometry w 2 (weightedMask w (· ≠ n) g.snd)) = 0
  rw [weightedMask_inner_complement,weightedMask_inner_complement,add_zero]

end NLS.ZakharovShabat
