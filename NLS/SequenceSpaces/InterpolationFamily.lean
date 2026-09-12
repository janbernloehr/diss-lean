import NLS.SequenceSpaces.FiniteCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Finite analytic coefficient families for interpolation

A complex phase times an exponential of the logarithmic magnitude gives an
entire power family, with zero coefficients kept zero. Its norms depend only
on the real part of the exponent. This is the input family for the finite
three-lines argument; no interpolation estimate is assumed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
open Complex

/-- Entire powers with the original phase and an identically zero branch at zero. -/
def powerCurve (a w : ℂ) : ℂ :=
  if a = 0 then 0 else (a / (‖a‖ : ℂ)) * exp (w * (Real.log ‖a‖ : ℂ))

@[simp] theorem powerCurve_zero (w : ℂ) : powerCurve 0 w = 0 := by simp [powerCurve]

@[simp] theorem powerCurve_one (a : ℂ) : powerCurve a 1 = a := by
  by_cases ha : a = 0
  · simp [ha]
  · simp only [powerCurve, if_neg ha, one_mul, ← Complex.ofReal_exp,
      Real.exp_log (norm_pos_iff.mpr ha)]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha))

theorem differentiable_powerCurve (a : ℂ) : Differentiable ℂ (powerCurve a) := by
  unfold powerCurve
  split_ifs
  · exact differentiable_const _
  · exact differentiable_const _ |>.mul ((differentiable_id.mul_const _).cexp)

/-- On the positive half-plane, the norm is the expected real power, including zero. -/
theorem norm_powerCurve (a w : ℂ) (hw : 0 < w.re) : ‖powerCurve a w‖ = ‖a‖ ^ w.re := by
  by_cases ha : a = 0
  · simp [ha, hw.ne']
  · simp only [powerCurve, if_neg ha, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha),
      one_mul, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr ha)]
    congr 1
    ring

/-- Finite powers retain a fixed finite frequency support. -/
def powerFamily (a : ℤ →₀ ℂ) (w : ℂ) : ℤ →₀ ℂ :=
  a.mapRange (fun z => powerCurve z w) (powerCurve_zero w)

@[simp] theorem powerFamily_apply (a : ℤ →₀ ℂ) (w : ℂ) (n : ℤ) :
    powerFamily a w n = powerCurve (a n) w := rfl

@[simp] theorem powerFamily_one (a : ℤ →₀ ℂ) : powerFamily a 1 = a := by
  ext n
  simp

theorem support_powerFamily_subset (a : ℤ →₀ ℂ) (w : ℂ) :
    (powerFamily a w).support ⊆ a.support := Finsupp.support_mapRange

/-- The affine reciprocal-exponent path on the unit strip. -/
def interpolationWeight (r p₀ p₁ : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) * ((1-z) / (p₀ : ℂ) + z / (p₁ : ℂ))

theorem interpolationWeight_re (r p₀ p₁ : ℝ) (z : ℂ) :
    (interpolationWeight r p₀ p₁ z).re = r * ((1-z.re)/p₀ + z.re/p₁) := by
  simp only [interpolationWeight, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_re, div_ofReal_re, sub_re, one_re]

theorem differentiable_interpolationWeight (r p₀ p₁ : ℝ) :
    Differentiable ℂ (interpolationWeight r p₀ p₁) :=
  differentiable_const _ |>.mul
    (((differentiable_const _).sub differentiable_id).div_const _ |>.add
      (differentiable_id.div_const _))

theorem interpolationWeight_re_pos {r p₀ p₁ : ℝ} (hr : 0 < r) (h₀ : 0 < p₀) (h₁ : 0 < p₁)
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1) : 0 < (interpolationWeight r p₀ p₁ z).re := by
  rw [interpolationWeight_re]
  apply mul_pos hr
  rcases eq_or_lt_of_le hz₀ with hz | hz
  · rw [← hz]; positivity
  · exact add_pos_of_nonneg_of_pos (div_nonneg (by linarith) h₀.le) (div_pos hz h₁)

theorem interpolationWeight_at {r p₀ p₁ t : ℝ}
    (h : r * ((1-t)/p₀ + t/p₁) = 1) : interpolationWeight r p₀ p₁ (t : ℂ) = 1 := by
  unfold interpolationWeight
  exact_mod_cast h

/-- Along a vertical edge, the finite family preserves the normalized power sum. -/
theorem norm_powerFamily_le_one {p r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hp : 0 < p.toReal) (hr : 0 < r.toReal) (a : ℤ →₀ ℂ)
    (ha : ‖ofFinsupp (p := r) a‖ ≤ 1) {w : ℂ} (hw : w.re = r.toReal / p.toReal) :
    ‖ofFinsupp (p := p) (powerFamily a w)‖ ≤ 1 := by
  apply lp.norm_le_of_tsum_le hp zero_le_one
  have hpos : 0 < w.re := by rw [hw]; exact div_pos hr hp
  have he : (∑' n : ℤ, ‖ofFinsupp (p := p) (powerFamily a w) n‖ ^ p.toReal) =
      ∑' n : ℤ, ‖ofFinsupp (p := r) a n‖ ^ r.toReal := by
    apply tsum_congr
    intro n
    rw [ofFinsupp_apply, powerFamily_apply, norm_powerCurve _ _ hpos,
      ← Real.rpow_mul (norm_nonneg _), hw, div_mul_cancel₀ _ hp.ne']
    rfl
  rw [he, ← lp.norm_rpow_eq_tsum hr, Real.one_rpow]
  exact Real.rpow_le_one (norm_nonneg _) ha hr.le

/-- Every coefficient stays in the unit disk throughout the strip for normalized input. -/
theorem norm_powerFamily_apply_le_one {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (a : ℤ →₀ ℂ) (ha : ‖ofFinsupp (p := r) a‖ ≤ 1) {w : ℂ} (hw : 0 < w.re) (n : ℤ) :
    ‖powerFamily a w n‖ ≤ 1 := by
  rw [powerFamily_apply, norm_powerCurve _ _ hw]
  apply Real.rpow_le_one (norm_nonneg _) _ hw.le
  exact (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ r)).ne'
    (ofFinsupp (p := r) a) n).trans ha

end NLS.Coeff
