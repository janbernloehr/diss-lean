import NLS.Fourier.ConjugateHilbert
import NLS.Fourier.HilbertInterpolation

/-!
# Discrete Hilbert boundedness for every `1 < p < ∞`

Dyadic estimates provide arbitrarily large upper endpoints and conjugate
dyadic estimates provide lower endpoints arbitrarily close to one. Finite
three-lines interpolation fills the intervening exponents. Density supplies
the ordinary and normalized shifted transforms on each entire `ℓp` space.
This proves the boundedness needed from Appendix C.1; invertibility is not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Intermediate exponents have an admissible affine reciprocal parameter. -/
theorem exists_interpolation_parameter {p₀ p₁ r : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hr₀ : p₀ ≤ r) (hr₁ : r ≤ p₁) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ r * ((1-t)/p₀ + t/p₁) = 1 := by
  let f := fun t : ℝ => r * ((1-t)/p₀ + t/p₁)
  have hf : Continuous f := by fun_prop
  have h₀ : 1 ≤ f 0 := by
    dsimp [f]
    simpa only [sub_zero, zero_div, add_zero, mul_one_div] using (le_div_iff₀ hp₀).mpr (by simpa using hr₀)
  have h₁ : f 1 ≤ 1 := by
    dsimp [f]
    simpa only [sub_self, zero_div, zero_add, mul_one_div] using (div_le_iff₀ hp₁).mpr (by simpa using hr₁)
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ⟨h₁, h₀⟩
  exact ⟨t, ht.1, ht.2, he⟩

/-- Choose an interpolation parameter between two proved endpoint estimates. -/
def HilbertEstimate.interpolateBetween {p₀ p₁ r : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ r)]
    (h₀ : HilbertEstimate p₀) (h₁ : HilbertEstimate p₁)
    (hr : 1 < r) (hrtop : r ≠ ⊤) (hr₀ : p₀.toReal ≤ r.toReal)
    (hr₁ : r.toReal ≤ p₁.toReal) : HilbertEstimate r := by
  have hp₀ := ENNReal.toReal_pos (zero_lt_one.trans h₀.one_lt).ne' h₀.ne_top
  have hp₁ := ENNReal.toReal_pos (zero_lt_one.trans h₁.one_lt).ne' h₁.ne_top
  let ht := exists_interpolation_parameter hp₀ hp₁ hr₀ hr₁
  exact h₀.interpolate h₁ hr hrtop (Classical.choose_spec ht).1
    (Classical.choose_spec ht).2.1 (Classical.choose_spec ht).2.2

/-- Every finite exponent strictly above one has a proved Hilbert estimate. -/
def hilbertEstimate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) :
    HilbertEstimate p := by
  have hpReal : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).mpr hp
  let hl := dyadicConjugateExponent_near_one hpReal
  let hu := dyadicHilbertExponent_unbounded p.toReal
  exact (conjugateHilbertEstimate (Classical.choose hl)).interpolateBetween
    (dyadicHilbertEstimate (Classical.choose hu)) hp hptop
    (Classical.choose_spec hl).le (Classical.choose_spec hu).le

/-- A finite, nonnegative bound for the ordinary transform at the chosen exponent. -/
def hilbertTransformBound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) : ℝ :=
  (hilbertEstimate hp hptop).bound

theorem hilbertTransformBound_nonneg {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) :
    0 ≤ hilbertTransformBound hp hptop := (hilbertEstimate hp hptop).bound_nonneg

/-- The ordinary discrete Hilbert transform on any finite Banach exponent above one. -/
def hilbertTransform {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) :
    Coeff p →L[ℂ] Coeff p := (hilbertEstimate hp hptop).operator

theorem hilbertTransform_finite {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : ℤ →₀ ℂ) (n : ℤ) : hilbertTransform hp hptop (Coeff.ofFinsupp a) n = finiteHilbert a n :=
  (hilbertEstimate hp hptop).operator_finite a n

theorem norm_hilbertTransform_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : Coeff p) : ‖hilbertTransform hp hptop a‖ ≤ hilbertTransformBound hp hptop * ‖a‖ :=
  (hilbertEstimate hp hptop).norm_operator_apply_le a

/-- The full-range construction agrees with any other completed estimate at the same exponent. -/
theorem hilbertTransform_eq_estimate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)
    (h : HilbertEstimate p) : hilbertTransform hp hptop = h.operator :=
  (hilbertEstimate hp hptop).operator_eq h

/-- The normalized shifted transform on every finite exponent strictly above one. -/
def shiftedHilbertTransform {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) :
    Coeff p →L[ℂ] Coeff p := (hilbertEstimate hp hptop).shifted

theorem shiftedHilbertTransform_finite {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : ℤ →₀ ℂ) (n : ℤ) : shiftedHilbertTransform hp hptop (Coeff.ofFinsupp a) n =
      a.sum (fun k z => z * (2 / ((Real.pi : ℂ) * (2*k - 2*n - 1)))) :=
  (hilbertEstimate hp hptop).shifted_finite a n

theorem norm_shiftedHilbertTransform_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hptop : p ≠ ⊤) (a : Coeff p) :
    ‖shiftedHilbertTransform hp hptop a‖ ≤
      Real.pi⁻¹ * (hilbertTransformBound hp hptop + ‖hilbertCorrectionCoeffs‖) * ‖a‖ :=
  (hilbertEstimate hp hptop).norm_shifted_apply_le a

/-- Full-range ordinary transforms satisfy the conjugate transposition identity. -/
theorem dualPairing_hilbertTransform {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : 1 < p) (hptop : p ≠ ⊤) (hq : 1 < q) (hqtop : q ≠ ⊤)
    (a : Coeff p) (b : Coeff q) :
    Coeff.dualPairing (hilbertTransform hp hptop a) b =
      -Coeff.dualPairing a (hilbertTransform hq hqtop b) :=
  (hilbertEstimate hp hptop).dualPairing_operator (hilbertEstimate hq hqtop) a b

end NLS.Fourier
