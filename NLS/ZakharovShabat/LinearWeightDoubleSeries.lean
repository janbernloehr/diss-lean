import NLS.ZakharovShabat.LinearWeightKernelPairing
import NLS.SequenceSpaces.LinearSpectralWeight
import NLS.SequenceSpaces.SpectralReflection

/-! # The actual weighted absolute double series in Lemma 25.2 -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The absolute coefficient series of the double complementary inverse, in
signed spectral coordinates (input frequency `-l`, output frequency `k`). -/
def linearWeightAbsoluteSeries (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 2)
    (n : ℤ) (z : ℂ) (p : ℤ × ℤ) : ℝ :=
  w (p.2-n)*‖complementarySymbol n z p.2‖*‖φ.val (p.2+p.1)‖*
    ‖complementarySymbol n z p.1‖*‖f.val (-p.1)‖

theorem linearWeightAbsoluteSeries_nonneg (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 2)
    (n : ℤ) (z : ℂ) (p : ℤ × ℤ) : 0 ≤ linearWeightAbsoluteSeries w φ f n z p := by
  unfold linearWeightAbsoluteSeries
  have := (w.positive (p.2-n)).le
  positivity

/-- The full absolute series is summable and obeys the exact scalar bound
in the proof of Lemma 25.2. No finiteness assumption is made on either source. -/
theorem summable_and_linearWeightAbsoluteSeries_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ f : WeightedCoeff w.toWeight 2) {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    Summable (linearWeightAbsoluteSeries w φ f n z) ∧
    (∑' p : ℤ × ℤ, linearWeightAbsoluteSeries w φ f n z p) ≤
      (4/(1+|(n:ℝ)|))*‖φ‖*w.shiftedNorm (-n) f := by
  let A := WeightedCoeff.weightEquiv w.toWeight 2 φ
  let B := Coeff.reflection (WeightedCoeff.weightEquiv (w.toWeight.shift (-n)) 2 (w.toShift (-n) f))
  have hA (k : ℤ) : ‖A k‖ = w k*‖φ.val k‖ := by
    simp only [A, WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (w.positive k)]
  have hB (l : ℤ) : ‖B l‖ = w (-l-n)*‖f.val (-l)‖ := by
    simp only [B, Coeff.reflection_apply, WeightedCoeff.weightEquiv_apply, SpectralWeight.toShift_apply,
      Weight.shift_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (w.positive _), ← sub_eq_add_neg]
  have h := summable_and_linearWeightKernel_pairing_le hz A B
  have hdom (p : ℤ × ℤ) : linearWeightAbsoluteSeries w φ f n z p ≤
      linearWeightKernel n z p.2 p.1*(‖A (p.2+p.1)‖*‖B p.1‖) := by
    rw [hA,hB]
    have hh := mul_le_mul_of_nonneg_right (SpectralWeight.linear_signed_ratio hw n p.2 p.1)
      (show 0 ≤ ‖complementarySymbol n z p.2‖*‖φ.val (p.2+p.1)‖*
        ‖complementarySymbol n z p.1‖*‖f.val (-p.1)‖ by positivity)
    convert! hh using 1 <;> simp only [linearWeightAbsoluteSeries, linearWeightKernel] <;> ring
  have hs := Summable.of_nonneg_of_le (linearWeightAbsoluteSeries_nonneg w φ f n z) hdom h.1
  refine ⟨hs, (Summable.tsum_le_tsum hdom hs h.1).trans ?_⟩
  have hnormA : ‖A‖ = ‖φ‖ := rfl
  have hnormB : ‖B‖ = w.shiftedNorm (-n) f := by
    dsimp only [B]
    rw [LinearIsometryEquiv.norm_map]
    rfl
  simpa only [hnormA,hnormB] using h.2

end NLS.ZakharovShabat
