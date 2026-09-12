import NLS.ZakharovShabat.ComplementaryL1
import NLS.ZakharovShabat.ResonantWindowGeometry
import NLS.SequenceSpaces.ReciprocalTail

/-!
# Uniform decay of the complementary reciprocal outside its near window

The central symbol is removed, so the estimates hold throughout the closed
strip, including at the lattice center. They apply to both physical signs and
to the `p=1` conjugate-infinity endpoint.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- A normalized inverse-bracket envelope for the unpunctured complementary symbol. -/
theorem complementarySymbol_bracket_bound {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (k : ℤ) :
    (1 / 2 : ℝ) * ‖complementarySymbol n z k‖ ≤ (1 + |((k - n : ℤ) : ℝ)|)⁻¹ := by
  by_cases hk : k = n
  · simp [hk]
  · have ha : 1 ≤ |((k-n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hk)
    have hd := resonantStrip_denominator_lower hz hk
    rw [complementarySymbol, if_neg hk, norm_inv]
    have hden : 0 < ‖z - (Real.pi : ℂ) * k‖ := zero_lt_one.trans_le (resonantStrip_denominator_one_le hz hk)
    rw [← div_eq_mul_inv, inv_eq_one_div]
    apply (div_le_div_iff₀ hden (by positivity)).mpr
    nlinarith

/-- The center of the reciprocal in physical coordinates. -/
def reciprocalCenter (b : Bool) (n : ℤ) : ℤ := freeFrequency b n

/-- Removing the near window gives uniform `|n|^(-1/p)` decay. -/
theorem norm_complementaryReciprocal_windowTail_le (hp : p ≠ ⊤) {n : ℤ} (hn : n ≠ 0)
    (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) :
    let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    let a := complementaryReciprocal hq n z hz b
    ‖a - Coeff.truncate (resonantWindow (reciprocalCenter b n)) a‖ ≤
      (16 * p.toReal) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) := by
  dsimp only
  have hN : 0 < n.natAbs := by omega
  have h := Coeff.norm_centered_reciprocal_windowTail_le_simple hp n.natAbs hN
    (reciprocalCenter b n) (r := 1/2) (by norm_num)
    (complementaryReciprocal ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) n z hz b)
    (fun k => ?_)
  · convert h using 1
    · congr 3
      cases b <;> simp [resonantWindow, reciprocalCenter]
    · ring
  · change (1/2 : ℝ) * ‖complementarySymbol n z (freeFrequency b k)‖ ≤ _
    have he : |((freeFrequency b k - n : ℤ) : ℝ)| = |((k - reciprocalCenter b n : ℤ) : ℝ)| := by
      cases b
      · rfl
      · simp only [freeFrequency_true, reciprocalCenter, Int.cast_sub, Int.cast_neg]
        rw [show -(k : ℝ) - n = -((k : ℝ) - -n) by ring, abs_neg]
    simpa only [he] using complementarySymbol_bracket_bound hz (freeFrequency b k)

end NLS.ZakharovShabat
