import NLS.SequenceSpaces.WeightedSandwichGain
import NLS.ZakharovShabat.ResonantWindowGeometry

/-!
# The scalar near/far estimate underlying Lemma 6.5

The far terms retain their full reciprocal-tail norms. The near-near term uses
exactly the source's weighted potential remainder divided by `w(n)`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The near-near sandwich gains the additional inverse resonant weight. -/
theorem shiftedNorm_near_sandwich_le (w : SpectralWeight) (n : ℤ) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm (-n) (w.sandwich (Coeff.truncate (resonantWindow n) a) φ
      (Coeff.truncate (resonantWindow (-n)) b) f) ≤
      (‖a‖ * ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ * ‖b‖ / w n) * w.shiftedNorm (-n) f := by
  rw [w.sandwich_truncate_eq_tail a φ b (resonantWindow n) (resonantWindow (-n)) n.natAbs
    (fun _ hj _ hk => resonantWindows_tail hj hk)]
  have h := w.shiftedNorm_sandwich_truncate_le_gain a
    (WeightedCoeff.fourierTail w.toWeight n.natAbs φ) b (resonantWindow n) (resonantWindow (-n)) (-n)
    (C := (w n)⁻¹) (inv_nonneg.mpr (w.positive n).le) (fun j hj k hk => ?_) f
  · convert h using 1
    ring
  · have h := resonantWindows_weight_ratio w hj hk
    simpa only [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Full scalar frequency split with the extra weight gain in the potential tail. -/
theorem shiftedNorm_sandwich_resonant_split (w : SpectralWeight) (n : ℤ) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm (-n) (w.sandwich a φ b f) ≤
      (‖a-Coeff.truncate (resonantWindow n) a‖ * ‖φ‖ * ‖b‖ +
        ‖a‖ * ‖φ‖ * ‖b-Coeff.truncate (resonantWindow (-n)) b‖ +
        ‖a‖ * ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ * ‖b‖ / w n) * w.shiftedNorm (-n) f := by
  let A := resonantWindow n
  let B := resonantWindow (-n)
  have ha : a = (a-Coeff.truncate A a) + Coeff.truncate A a := by abel
  have hb : b = (b-Coeff.truncate B b) + Coeff.truncate B b := by abel
  have he : w.sandwich a φ b = w.sandwich (a-Coeff.truncate A a) φ b +
      w.sandwich (Coeff.truncate A a) φ (b-Coeff.truncate B b) +
      w.sandwich (Coeff.truncate A a) φ (Coeff.truncate B b) := by
    conv_lhs => rw [ha, SpectralWeight.sandwich_add_left]
    conv_lhs => rhs; rw [hb, SpectralWeight.sandwich_add_right]
    rw [add_assoc]
  rw [he]
  change w.shiftedNorm (-n) (_ + _ + _) ≤ _
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  have hf0 : 0 ≤ w.shiftedNorm (-n) f := norm_nonneg _
  calc
    _ ≤ w.shiftedNorm (-n) (w.sandwich (a-Coeff.truncate A a) φ b f) +
        w.shiftedNorm (-n) (w.sandwich (Coeff.truncate A a) φ (b-Coeff.truncate B b) f) +
        w.shiftedNorm (-n) (w.sandwich (Coeff.truncate A a) φ (Coeff.truncate B b) f) :=
      (w.shiftedNorm_add_triangle (-n) _ _).trans (add_le_add (w.shiftedNorm_add_triangle (-n) _ _) le_rfl)
    _ ≤ _ := by
      rw [add_mul, add_mul]
      apply add_le_add
      · apply add_le_add
        · exact w.shiftedNorm_sandwich_le _ _ _ (-n) f
        · apply (w.shiftedNorm_sandwich_le _ _ _ (-n) f).trans
          gcongr
          exact Coeff.norm_truncate_le hq0 A a
      · exact shiftedNorm_near_sandwich_le w n a φ b f

/-- A common reciprocal bound and a common tail bound isolate both source contributions. -/
theorem shiftedNorm_sandwich_resonant_split_of_bounds (w : SpectralWeight) (n : ℤ) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) {U V : ℝ}
    (ha : ‖a‖ ≤ U) (hb : ‖b‖ ≤ U)
    (haT : ‖a-Coeff.truncate (resonantWindow n) a‖ ≤ V)
    (hbT : ‖b-Coeff.truncate (resonantWindow (-n)) b‖ ≤ V)
    (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm (-n) (w.sandwich a φ b f) ≤
      (2 * U * V * ‖φ‖ + U ^ 2 * ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ / w n) * w.shiftedNorm (-n) f := by
  have hU : 0 ≤ U := (norm_nonneg _).trans ha
  have hV : 0 ≤ V := (norm_nonneg _).trans haT
  have hf0 : 0 ≤ w.shiftedNorm (-n) f := norm_nonneg _
  have hw0 : 0 < w n := w.positive n
  apply (shiftedNorm_sandwich_resonant_split w n a φ b f).trans
  apply mul_le_mul_of_nonneg_right _ hf0
  calc
    _ ≤ V * ‖φ‖ * U + U * ‖φ‖ * V + U * ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ * U / w n := by gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
