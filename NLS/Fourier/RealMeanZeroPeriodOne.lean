import NLS.Fourier.PeriodicDistributionParity
import NLS.Fourier.NativePeriodicConjugation

/-! # Real mean-zero period-one original distributions

Reality is equality with conjugation on every smooth test. Period one means
invariance of the associated tempered distribution under translation by one.
Both conditions are identified with the actual normalized period-two Fourier
coefficients; no measure or finite-exponent hypothesis is imposed.
-/
noncomputable section
open scoped SchwartzMap
namespace NLS.Fourier.SmoothPeriodicTest.Distribution

/-- The physical real mean-zero period-one distribution locus. -/
def IsRealMeanZeroPeriodOne (u : Distribution (2:ℝ)) : Prop :=
  u = u.conjugate ∧ u (mode 0) = 0 ∧ IsPeriodicDistribution 1 u.toTempered

/-- Exact normalized coefficient characterization of the physical source locus. -/
theorem isRealMeanZeroPeriodOne_iff_coefficients (u : Distribution (2:ℝ)) :
    IsRealMeanZeroPeriodOne u ↔
      u (mode 0) = 0 ∧
      (∀ n : ℤ, u (mode n) = star (u (mode (-n)))) ∧
      ∀ k : ℤ, u (mode (-(2*k+1))) = 0 := by
  rw [IsRealMeanZeroPeriodOne, eq_conjugate_iff_coefficients,
    toTempered_period_one_iff_odd]
  constructor
  · rintro ⟨hr,h0,hp⟩
    refine ⟨h0, ?_, hp⟩
    intro n
    simpa only [neg_neg] using hr (-n)
  · rintro ⟨h0,hr,hp⟩
    refine ⟨?_,h0,hp⟩
    intro n
    simpa only [neg_neg] using hr (-n)

end NLS.Fourier.SmoothPeriodicTest.Distribution
