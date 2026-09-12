import NLS.ZakharovShabat.VerticalStrips
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The unpunctured Section 6 strip and complementary free symbol

Removing the resonant frequency leaves all free denominators uniformly away
from zero throughout the closed strip, including at its central lattice point.
The complementary symbol is explicitly zero at the removed frequency.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The entire closed vertical strip `U_n` in Section 6, with no central disk removed. -/
def resonantStrip (n : ℤ) : Set ℂ := {z | |z.re - Real.pi * n| ≤ Real.pi / 2}

@[simp] theorem center_mem_resonantStrip (n : ℤ) : (Real.pi : ℂ) * n ∈ resonantStrip n := by
  simp only [resonantStrip, Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re,
    Complex.intCast_re, Complex.ofReal_im, Complex.intCast_im, mul_zero, sub_zero, sub_self, abs_zero]
  positivity

/-- All nonresonant free denominators dominate the integer distance in the closed strip. -/
theorem resonantStrip_denominator_lower {n m : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (hm : m ≠ n) :
    |((m - n : ℤ) : ℝ)| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  have habs : 1 ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  have htri : Real.pi * |((m - n : ℤ) : ℝ)| ≤ |z.re - Real.pi * m| + |z.re - Real.pi * n| := by
    have h := norm_sub_le (z.re - Real.pi * m) (z.re - Real.pi * n)
    have he : (z.re - Real.pi * m) - (z.re - Real.pi * n) = -Real.pi * ((m - n : ℤ) : ℝ) := by push_cast; ring
    simpa only [he, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using h
  have hre : |z.re - Real.pi * m| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
    simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * m)
  have hπ : 2 ≤ Real.pi := by linarith [Real.pi_gt_three]
  change |z.re - Real.pi * n| ≤ Real.pi / 2 at hz
  nlinarith

theorem resonantStrip_denominator_one_le {n m : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (hm : m ≠ n) :
    1 ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  have h : 1 ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  exact h.trans (resonantStrip_denominator_lower hz hm)

theorem resonantStrip_denominator_ne_zero {n m : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (hm : m ≠ n) :
    z - (Real.pi : ℂ) * m ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (resonantStrip_denominator_one_le hz hm))

/-- Reciprocal free symbol with the resonant coefficient removed, even when `z=nπ`. -/
def complementarySymbol (n : ℤ) (z : ℂ) (m : ℤ) : ℂ := if m = n then 0 else (z - (Real.pi : ℂ) * m)⁻¹

@[simp] theorem complementarySymbol_resonant (n : ℤ) (z : ℂ) : complementarySymbol n z n = 0 := by simp [complementarySymbol]

theorem norm_complementarySymbol_le {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (m : ℤ) :
    ‖complementarySymbol n z m‖ ≤ 1 := by
  by_cases hm : m = n
  · simp [complementarySymbol, hm]
  · rw [complementarySymbol, if_neg hm, norm_inv]
    simpa only [inv_one] using inv_anti₀ zero_lt_one (resonantStrip_denominator_one_le hz hm)

/-- A finite bound for the complementary inverse into the one-derivative domain. -/
def complementaryDomainBound (z : ℂ) : ℝ := 1 + (1 + ‖z‖) / Real.pi

theorem complementaryDomainBound_nonneg (z : ℂ) : 0 ≤ complementaryDomainBound z := by unfold complementaryDomainBound; positivity

theorem weighted_complementarySymbol_le {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (m : ℤ) :
    (1 + |(m : ℝ)|) * ‖complementarySymbol n z m‖ ≤ complementaryDomainBound z := by
  by_cases hm : m = n
  · simp only [complementarySymbol, if_pos hm, norm_zero, mul_zero]
    exact complementaryDomainBound_nonneg z
  · have hd := resonantStrip_denominator_one_le hz hm
    have hn : Real.pi * |(m : ℝ)| ≤ ‖z - (Real.pi : ℂ) * m‖ + ‖z‖ := by
      have h := norm_sub_le (z - (Real.pi : ℂ) * m) z
      simpa [sub_sub_cancel_left, norm_mul, abs_of_pos Real.pi_pos] using h
    rw [complementarySymbol, if_neg hm, norm_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    unfold complementaryDomainBound
    have hπ := Real.pi_pos
    have hzN := norm_nonneg z
    field_simp
    nlinarith

/-- Multiplying back by the free denominator gives exactly the complementary frequency mask. -/
theorem denominator_mul_complementarySymbol {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (m : ℤ) :
    (z - (Real.pi : ℂ) * m) * complementarySymbol n z m = if m = n then 0 else 1 := by
  by_cases hm : m = n
  · simp [complementarySymbol, hm]
  · simp only [complementarySymbol, if_neg hm, mul_inv_cancel₀ (resonantStrip_denominator_ne_zero hz hm)]

end NLS.ZakharovShabat
