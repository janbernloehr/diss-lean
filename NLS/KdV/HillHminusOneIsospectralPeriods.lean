import NLS.KdV.HillHminusOneIsospectralPrimitive
import NLS.KdV.HillHminusOneAllPeriodZeros

/-! # Actual canonical periods are real isospectral invariants

Equality of the full discriminants fixes the contour geometry and the
source-normalized primitive. This includes central and collapsed gaps.
No equality between actions and discriminants is assumed or asserted.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem hillHminusRealGapPrimitiveSquare_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) (n : ℕ) :
    hillHminusRealGapPrimitiveSquare q n = hillHminusRealGapPrimitiveSquare p n := by
  funext z
  simp only [hillHminusRealGapPrimitiveSquare,
    hillHminusRealCutPrimitive_eq_of_discriminant_eq q p hq hp hD]

/-- Polynomial and cubic periods with their exact physical normalizations
are invariants of the entire real discriminant. -/
theorem hillHminusRealGapContourMoments_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) (n : ℕ+) :
    (∀ m, hillHminusRealGapContourMoment q hq n m = hillHminusRealGapContourMoment p hp n m) ∧
      hillHminusRealGapCubicContourMoment q hq n = hillHminusRealGapCubicContourMoment p hp n := by
  have hlabels := hillHminusRealLabels_eq_of_discriminant_eq q p hq hp hD
  have hF := hillHminusRealCutPrimitive_eq_of_discriminant_eq q p hq hp hD
  constructor
  · intro m
    simp only [hillHminusRealGapContourMoment,hillHminusRealGapCenter,
      hillHminusRealGapHalfLength,hillHminusRealGapCollar,hlabels,hF]
  · simp only [hillHminusRealGapCubicContourMoment,hillHminusRealGapCenter,
      hillHminusRealGapHalfLength,hillHminusRealGapCollar,hlabels,hF]

end NLS.KdV
