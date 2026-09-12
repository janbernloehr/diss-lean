import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.PairNorm

/-!
# Section 6's signed shifted pair norm

In physical Fourier coordinates the first component is modulated by `-i`
and the second by `i`. Reindexing the first component by frequency reflection
gives exactly the combined signed coefficient formula in the source.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Opposite modulations on the two physical components implement the source's signed shift. -/
def pairModulation (w : SpectralWeight) (i : ℤ) : WeightedCoeffPair w.toWeight p ≃L[ℂ] WeightedCoeffPair w.toWeight p :=
  ((WeightedCoeffPair.toMax w.toWeight p).trans
    ((modulation w (-i)).prodCongr (modulation w i))).trans (WeightedCoeffPair.toMax w.toWeight p).symm

@[simp] theorem pairModulation_fst (w : SpectralWeight) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    (pairModulation w i f).fst = modulation w (-i) f.fst := rfl

@[simp] theorem pairModulation_snd (w : SpectralWeight) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    (pairModulation w i f).snd = modulation w i f.snd := rfl

/-- The shifted finite-exponent pair norm from Section 6, using the original physical coefficients. -/
def shiftedPairNorm (w : SpectralWeight) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) : ℝ := ‖pairModulation w i f‖

/-- Its exponent power is the sum of the two oppositely shifted scalar energies. -/
theorem shiftedPairNorm_rpow (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    shiftedPairNorm w i f ^ p.toReal = shiftedNorm w (-i) f.fst ^ p.toReal + shiftedNorm w i f.snd ^ p.toReal := by
  rw [shiftedPairNorm, norm_withLp_prod_rpow hp, pairModulation_fst, pairModulation_snd, norm_modulation, norm_modulation]

/-- Exact signed coefficient formula: the first physical sequence is reflected at `-n`. -/
theorem shiftedPairNorm_rpow_eq_tsum (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    shiftedPairNorm w i f ^ p.toReal = ∑' n : ℤ, w (n + i) ^ p.toReal *
      (‖f.fst.val (-n)‖ ^ p.toReal + ‖f.snd.val n‖ ^ p.toReal) := by
  have he (n : ℤ) : w (-n + -i) = w (n + i) := by rw [← neg_add, apply_neg]
  have h₁ : Summable (fun n : ℤ => w (n + i) ^ p.toReal * ‖f.fst.val (-n)‖ ^ p.toReal) := by
    have h := (Equiv.neg ℤ).summable_iff.mpr (summable_shiftedNorm_terms w hp (-i) f.fst)
    simpa only [Function.comp_def, Equiv.neg_apply, he] using h
  have h₂ := summable_shiftedNorm_terms w hp i f.snd
  rw [shiftedPairNorm_rpow w hp, shiftedNorm_rpow_eq_tsum w hp, shiftedNorm_rpow_eq_tsum w hp,
    ← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => w (n + -i) ^ p.toReal * ‖f.fst.val n‖ ^ p.toReal)]
  simp only [Equiv.neg_apply, he]
  rw [← h₁.tsum_add h₂]
  apply tsum_congr
  intro n
  exact (mul_add _ _ _).symm

/-- The comparison factor for the whole finite-`p` pair is `w(i)`, without an extra pair-norm loss. -/
theorem shiftedPairNorm_le (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    shiftedPairNorm w i f ≤ w i * ‖f‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hw : 0 < w i := w.positive i
  rw [shiftedPairNorm, WithLp.prod_norm_eq_add hp0]
  change (‖modulation w (-i) f.fst‖ ^ p.toReal + ‖modulation w i f.snd‖ ^ p.toReal) ^ (1 / p.toReal) ≤ _
  calc
    _ ≤ ((w i * ‖f.fst‖) ^ p.toReal + (w i * ‖f.snd‖) ^ p.toReal) ^ (1 / p.toReal) := by
      gcongr
      · simpa only [apply_neg] using norm_modulation_le w (-i) f.fst
      · exact norm_modulation_le w i f.snd
    _ = w i * ‖f‖ := by
      rw [Real.mul_rpow (w.positive i).le (norm_nonneg _), Real.mul_rpow (w.positive i).le (norm_nonneg _),
        ← mul_add, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (w.positive i).le,
        mul_one_div_cancel hp0.ne', Real.rpow_one, ← WithLp.prod_norm_eq_add hp0]

/-- The signed pair modulations obey addition of their indices. -/
theorem pairModulation_add (w : SpectralWeight) (i j : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    pairModulation w (i + j) f = pairModulation w j (pairModulation w i f) := by
  apply (WithLp.ext_iff p).mpr
  apply Prod.ext
  · change modulation w (-(i + j)) f.fst = modulation w (-j) (modulation w (-i) f.fst)
    rw [neg_add, modulation_add]
  · exact modulation_add w i j f.snd

@[simp] theorem pairModulation_zero (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight p) : pairModulation w 0 f = f := by
  apply (WithLp.ext_iff p).mpr
  apply Prod.ext
  · change modulation w (-0) f.fst = f.fst
    simp only [neg_zero, modulation_zero]
  · exact modulation_zero w f.snd

@[simp] theorem shiftedPairNorm_zero (w : SpectralWeight) (f : WeightedCoeffPair w.toWeight p) : shiftedPairNorm w 0 f = ‖f‖ := by
  rw [shiftedPairNorm, pairModulation_zero]

/-- Reverse comparison retains the same factor, since the inverse shift has the same weight. -/
theorem norm_le_shiftedPairNorm (w : SpectralWeight) (hp : p ≠ ⊤) (i : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    ‖f‖ ≤ w i * shiftedPairNorm w i f := by
  have h := shiftedPairNorm_le w hp (-i) (pairModulation w i f)
  simpa only [shiftedPairNorm, ← pairModulation_add, add_neg_cancel, pairModulation_zero, apply_neg] using h

end NLS.SpectralWeight
