import NLS.ZakharovShabat.ComplementaryReciprocalTail
import NLS.ZakharovShabat.WeightedResonantSandwich
import NLS.ZakharovShabat.WeightedPotentialInverse

/-!
# Weighted double-complementary inverse estimate

The scalar inner part of `T_n²` obeys the two terms in Lemma 6.5. The estimate
holds on the entire closed strip, with either physical sign, including the
zero strip and the Banach endpoint `p=1`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

@[simp] theorem reciprocalCenter_not (b : Bool) (n : ℤ) :
    reciprocalCenter (!b) n = -reciprocalCenter b n := by cases b <;> simp [reciprocalCenter]

/-- The scalar double inverse, with the off-diagonal potential between opposite free signs. -/
def complementarySandwich (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeff w.toWeight p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff w.toWeight 1 :=
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  w.sandwich (complementaryReciprocal hq n z hz b) φ (complementaryReciprocal hq n z hz (!b))

@[simp] theorem complementarySandwich_apply (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeff w.toWeight p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) (f : WeightedCoeff w.toWeight p) (j : ℤ) :
    (complementarySandwich hp w φ n z hz b f).val j = complementarySymbol n z (freeFrequency b j) *
      ∑' k : ℤ, φ.val (j-k) * (complementarySymbol n z (freeFrequency (!b) k) * f.val k) := by
  simp only [complementarySandwich, SpectralWeight.sandwich_apply, complementaryReciprocal_apply]

/-- The coarse bound, used for the zero strip. -/
theorem shiftedNorm_complementarySandwich_le (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeff w.toWeight p)
    (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (complementarySandwich hp w φ n z hz b f) ≤
      (Coeff.complementaryConstant p hp ^ 2 * ‖φ‖) * w.shiftedNorm i f := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hfull (b : Bool) : ‖complementaryReciprocal hq n z hz b‖ ≤ Coeff.complementaryConstant p hp :=
    (norm_complementaryReciprocal_le hq n z hz b).trans (Coeff.norm_puncturedLattice_le_complementaryConstant p hp)
  apply (w.shiftedNorm_sandwich_le (complementaryReciprocal hq n z hz b) φ
    (complementaryReciprocal hq n z hz (!b)) i f).trans
  have hC := Coeff.complementaryConstant_nonneg p hp
  have hf0 : 0 ≤ w.shiftedNorm i f := norm_nonneg _
  calc
    _ ≤ (Coeff.complementaryConstant p hp * ‖φ‖ * Coeff.complementaryConstant p hp) * w.shiftedNorm i f := by gcongr <;> exact hfull _
    _ = _ := by ring

/-- The two scalar source contributions, retaining a separate constant for each. -/
theorem shiftedNorm_complementarySandwich_le_frequency_split (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeff w.toWeight p) {n : ℤ} (hn : n ≠ 0) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm (-reciprocalCenter b n) (complementarySandwich hp w φ n z hz b f) ≤
      (32 * p.toReal * Coeff.complementaryConstant p hp * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) * ‖φ‖ +
        Coeff.complementaryConstant p hp ^ 2 * ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ / w n) *
        w.shiftedNorm (-reciprocalCenter b n) f := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hfull (s : Bool) : ‖complementaryReciprocal hq n z hz s‖ ≤ Coeff.complementaryConstant p hp :=
    (norm_complementaryReciprocal_le hq n z hz s).trans (Coeff.norm_puncturedLattice_le_complementaryConstant p hp)
  have hout := norm_complementaryReciprocal_windowTail_le hp hn z hz b
  have hin := norm_complementaryReciprocal_windowTail_le hp hn z hz (!b)
  dsimp only at hout hin
  rw [reciprocalCenter_not] at hin
  have h := shiftedNorm_sandwich_resonant_split_of_bounds w (reciprocalCenter b n)
    (complementaryReciprocal hq n z hz b) φ (complementaryReciprocal hq n z hz (!b))
    (hfull b) (hfull (!b)) hout hin f
  have habs : (reciprocalCenter b n).natAbs = n.natAbs := by cases b <;> simp [reciprocalCenter]
  have hw : w (reciprocalCenter b n) = w n := by cases b <;> simp [reciprocalCenter]
  rw [habs, hw] at h
  convert h using 1 <;> first | rfl | ring

/-- A uniform exponent-only constant for the refined double inverse. -/
def weightedDoubleConstant (hp : p ≠ ⊤) : ℝ :=
  64 * p.toReal * Coeff.complementaryConstant p hp + Coeff.complementaryConstant p hp ^ 2

theorem weightedDoubleConstant_nonneg (hp : p ≠ ⊤) : 0 ≤ weightedDoubleConstant (p := p) hp := by
  have hC := Coeff.complementaryConstant_nonneg p hp
  unfold weightedDoubleConstant
  positivity

private theorem full_radius_to_bracket (hp : p ≠ ⊤) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / p.toReal)) ≤ 2 * (1 + (N : ℝ)) ^ (-(1 / p.toReal)) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ((1 + (N : ℝ)) / 2) ^ (-(1 / p.toReal)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (by positivity))
    _ ≤ _ := Coeff.half_radius_rpow_le hp1 (by positivity)

/-- Scalar Lemma 6.5 bound, with the inhomogeneous bracket and the exact inverse-weight tail gain. -/
theorem shiftedNorm_complementarySandwich_le_refined (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (b : Bool) (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm (-reciprocalCenter b n) (complementarySandwich hp w φ n z hz b f) ≤
      (weightedDoubleConstant (p := p) hp * (‖φ‖ * (1 + |(n : ℝ)|) ^ (-(1 / p.toReal)) +
        ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ / w n)) * w.shiftedNorm (-reciprocalCenter b n) f := by
  have hC := Coeff.complementaryConstant_nonneg p hp
  have hp0 := ENNReal.toReal_nonneg (a := p)
  have hf0 : 0 ≤ w.shiftedNorm (-reciprocalCenter b n) f := norm_nonneg _
  have hw0 := w.positive n
  have hD : Coeff.complementaryConstant p hp ^ 2 ≤ weightedDoubleConstant (p := p) hp := by
    unfold weightedDoubleConstant
    exact le_add_of_nonneg_left (by positivity)
  by_cases hn : n = 0
  · subst n
    apply (shiftedNorm_complementarySandwich_le hp w φ _ 0 z hz b f).trans
    apply mul_le_mul_of_nonneg_right _ hf0
    simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, mul_one]
    calc
      _ ≤ weightedDoubleConstant (p := p) hp * ‖φ‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (weightedDoubleConstant_nonneg hp)
  · apply (shiftedNorm_complementarySandwich_le_frequency_split hp w φ hn z hz b f).trans
    apply mul_le_mul_of_nonneg_right _ hf0
    have hN := full_radius_to_bracket hp (show 0 < n.natAbs by omega)
    have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [habs] at hN
    rw [habs]
    have hD' : 64 * p.toReal * Coeff.complementaryConstant p hp ≤ weightedDoubleConstant (p := p) hp := by
      unfold weightedDoubleConstant
      exact le_add_of_nonneg_right (sq_nonneg _)
    calc
      _ ≤ (64 * p.toReal * Coeff.complementaryConstant p hp) * (‖φ‖ * (1 + |(n : ℝ)|) ^ (-(1 / p.toReal))) +
          Coeff.complementaryConstant p hp ^ 2 * (‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ / w n) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN
          (show 0 ≤ 32 * p.toReal * Coeff.complementaryConstant p hp by positivity)) (norm_nonneg φ)
        convert add_le_add h (le_refl (Coeff.complementaryConstant p hp ^ 2 *
          (‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖ / w n))) using 1 <;> first | rfl | ring
      _ ≤ _ := by rw [mul_add]; gcongr

end NLS.ZakharovShabat
