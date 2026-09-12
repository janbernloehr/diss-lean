import NLS.SequenceSpaces.Insertion
import NLS.Fourier.HilbertSeries

/-!
# The bounded half-interval Fourier map

Insert half the original input at even indices and half the normalized shifted
Hilbert image times `i` at odd indices. The result agrees with the physical
half-interval Fourier integrals on finite polynomials and is bounded for every
`1<p<∞`, with the normalization derived from equations (1.8)–(1.9).
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)

/-- The completed half-interval Fourier coefficients in the period-two convention. -/
def halfIntervalCoeffs : Coeff p →L[ℂ] Coeff p :=
  (1/2 : ℂ) • (Coeff.insertIsometry (Coeff.parityEmbedding 0)).toContinuousLinearMap +
    (I/2 : ℂ) • ((Coeff.insertIsometry (Coeff.parityEmbedding 1)).toContinuousLinearMap.comp
      (shiftedHilbertTransform hp hptop))

/-- A sufficient operator bound for the normalized half-interval map. -/
def halfIntervalBound : ℝ :=
  (1 + Real.pi⁻¹ * (hilbertTransformBound hp hptop + ‖hilbertCorrectionCoeffs‖)) / 2

theorem halfIntervalBound_pos : 0 < halfIntervalBound hp hptop := by
  have := hilbertTransformBound_nonneg hp hptop
  unfold halfIntervalBound
  positivity

theorem norm_halfIntervalCoeffs_apply_le (a : Coeff p) :
    ‖halfIntervalCoeffs hp hptop a‖ ≤ halfIntervalBound hp hptop * ‖a‖ := by
  change ‖(1/2 : ℂ) • Coeff.insert (Coeff.parityEmbedding 0) a +
    (I/2 : ℂ) • Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a)‖ ≤ _
  calc
    _ ≤ ‖(1/2 : ℂ) • Coeff.insert (Coeff.parityEmbedding 0) a‖ +
        ‖(I/2 : ℂ) • Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a)‖ :=
      norm_add_le _ _
    _ = (1/2 : ℝ) * ‖a‖ + (1/2 : ℝ) * ‖shiftedHilbertTransform hp hptop a‖ := by
      simp only [norm_smul, Coeff.norm_insert]
      norm_num [norm_div]
    _ ≤ (1/2 : ℝ) * ‖a‖ + (1/2 : ℝ) *
        (Real.pi⁻¹ * (hilbertTransformBound hp hptop + ‖hilbertCorrectionCoeffs‖) * ‖a‖) := by
      gcongr
      exact norm_shiftedHilbertTransform_apply_le hp hptop a
    _ = _ := by unfold halfIntervalBound; ring

/-- Even output coefficients retain half of the corresponding input. -/
theorem halfIntervalCoeffs_even (a : Coeff p) (n : ℤ) :
    halfIntervalCoeffs hp hptop a (2*n) = (1/2 : ℂ) * a n := by
  change (1/2 : ℂ) * Coeff.insert (Coeff.parityEmbedding 0) a (2*n) +
    (I/2 : ℂ) * Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a) (2*n) = _
  have he : Coeff.insert (Coeff.parityEmbedding 0) a (2*n) = a n := by
    simpa using Coeff.insert_apply_image (Coeff.parityEmbedding 0) a n
  have ho : Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a) (2*n) = 0 := by
    simpa using Coeff.insert_parity_other 1 0 (by norm_num) (shiftedHilbertTransform hp hptop a) n
  rw [he, ho, mul_zero, add_zero]

/-- Odd output coefficients are the normalized shifted Hilbert contribution. -/
theorem halfIntervalCoeffs_odd (a : Coeff p) (n : ℤ) :
    halfIntervalCoeffs hp hptop a (2*n+1) = (I/2 : ℂ) * shiftedHilbertTransform hp hptop a n := by
  change (1/2 : ℂ) * Coeff.insert (Coeff.parityEmbedding 0) a (2*n+1) +
    (I/2 : ℂ) * Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a) (2*n+1) = _
  have he := Coeff.insert_parity_other 0 1 (by norm_num) a n
  have ho := Coeff.insert_apply_image (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a) n
  change Coeff.insert (Coeff.parityEmbedding 1) (shiftedHilbertTransform hp hptop a) (2*n+1) = _ at ho
  rw [he, ho, mul_zero, zero_add]

/-- The bounded map agrees with the physical finite Fourier construction. -/
theorem halfIntervalCoeffs_finite (a : ℤ →₀ ℂ) :
    halfIntervalCoeffs hp hptop (Coeff.ofFinsupp a) = polynomialHalfCoeffs hp a := by
  apply lp.ext
  funext n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, halfIntervalCoeffs_even, polynomialHalfCoeffs_apply, halfCoefficient_polynomial_even]
    rfl
  · have he : n = 2*(n/2)+1 := by omega
    rw [he, halfIntervalCoeffs_odd, shiftedHilbertTransform_finite,
      polynomialHalfCoeffs_apply, halfCoefficient_polynomial_odd]
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

/-- Every finite output coefficient is the normalized integral over the input interval. -/
theorem halfIntervalCoeffs_finite_integral (a : ℤ →₀ ℂ) (n : ℤ) :
    halfIntervalCoeffs hp hptop (Coeff.ofFinsupp a) n = halfCoefficient (polynomial a) n := by
  rw [halfIntervalCoeffs_finite, polynomialHalfCoeffs_apply]

/-- The even coefficients recover every original coefficient. -/
theorem halfIntervalCoeffs_injective : Function.Injective (halfIntervalCoeffs hp hptop) := by
  intro a b h
  apply lp.ext
  funext n
  have he := congrArg (fun c : Coeff p => c (2*n)) h
  simp only [halfIntervalCoeffs_even] at he
  exact mul_left_cancel₀ (by norm_num : (1/2 : ℂ) ≠ 0) he

end NLS.Fourier
