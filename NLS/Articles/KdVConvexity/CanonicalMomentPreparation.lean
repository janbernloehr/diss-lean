import NLS.KdV.HillHminusOneAllPeriodZeros

/-! # Actual finite-head spectral inputs for the convexity moment extension

For any finite positive-index head, one complex H^-1 neighborhood carries
analytic canonical Arnold and cubic periods. At all nearby real inputs,
Arnold periods are nonnegative, cubic periods are nonpositive and real,
and their zero sets agree exactly. Identification with global Birkhoff
actions and real isospectral invariance remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

/-- The finite-head analytic and sign/zero inputs for the actual spectral
moments of Lemma 4.6, before Birkhoff-action identification. -/
theorem exists_finite_analytic_canonical_periods_with_signs
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (S : Finset ℕ+) :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ q ∈ W ∧
      ∃ A : ℕ+ → ℕ → PeriodOneHminusOne → ℂ, ∃ R : ℕ+ → PeriodOneHminusOne → ℂ,
        ∀ n ∈ S, (∀ m, AnalyticOnNhd ℂ (A n m) W) ∧ AnalyticOnNhd ℂ (R n) W ∧
          ∀ p ∈ W, ∀ hp : IsRealPeriodOneHminusOne p,
            (∀ m, A n m p = hillHminusRealGapContourMoment p hp n m) ∧
            R n p = hillHminusRealGapCubicContourMoment p hp n ∧
            0 ≤ (A n 0 p).re ∧ (R n p).re ≤ 0 ∧ (R n p).im = 0 ∧
            (R n p = 0 ↔ A n 0 p = 0) := by
  obtain ⟨W,hW,hq,A,R,hdata⟩ := exists_hillHminus_finite_canonical_period_extensions q hr S
  refine ⟨W,hW,hq,A,R,?_⟩
  intro n hn
  obtain ⟨hA,hR,hmatch⟩ := hdata n hn
  refine ⟨hA,hR,?_⟩
  intro p hp hpr
  obtain ⟨hAm,hRm⟩ := hmatch p hp hpr
  refine ⟨hAm,hRm,?_,?_,?_,?_⟩
  · rw [hAm 0]
    simpa only [Nat.mul_zero] using hillHminusRealGapContourMoment_even_nonneg p hpr n 0
  · rw [hRm]
    exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).1
  · rw [hRm]
    exact (hillHminusRealGapCubicContourMoment_nonpositive p hpr n).2
  · rw [hRm,hAm 0]
    exact hillHminusRealGapCubicContourMoment_eq_zero_iff_Arnold_zero p hpr n

end NLS.Articles.KdVConvexity
