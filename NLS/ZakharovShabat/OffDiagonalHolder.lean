import NLS.ZakharovShabat.WeightedDoubleRow
import NLS.ZakharovShabat.OffDiagonalSeries
import NLS.ZakharovShabat.ResonantEvenBounds

/-!
# Weighted Hölder estimates for the actual off-diagonal remainders

The physical Fourier identities and the weighted two-index test retain the
source component norms and the double reciprocal row. Both source coefficient
labels are covered without a reality assumption on the potential.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] in
/-- Reindex the physical source series into the normalized reciprocal coordinates. -/
theorem tsum_weightedOffDiagonalTerm_eq (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p)
    (n : ℤ) (z : ℂ) :
    (∑' j : ℤ, ∑' k : ℤ, weightedOffDiagonalTerm w d a f n z j k) =
      (w (2*n) : ℂ) * ∑' l : ℤ, ∑' k : ℤ, d.val (n+l) * a.val (l+k) *
        complementarySymbol n z l * complementarySymbol n z k * f.val k := by
  rw [← (Equiv.subLeft n).tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro l
  rw [← (Equiv.subLeft n).tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  change (w (2*n) : ℂ) * d.val (2*n-(n-l)) * a.val (2*n-(n-l)-(n-k)) *
    complementarySymbol n z (n-(n-l)) * complementarySymbol n z (n-(n-k)) * f.val (n-(n-k)) = _
  rw [show 2*n-(n-l) = n+l by ring, show n+l-(n-k) = l+k by ring,
    sub_sub_cancel, sub_sub_cancel]
  ring

/-- The physical double Fourier series is absolutely convergent jointly in its two indices. -/
theorem summable_norm_offDiagonal_terms [p.HolderConjugate q] (hq : 1 < q)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    Summable (fun lk : ℤ × ℤ => ‖d.val (n+lk.1) * a.val (lk.1+lk.2) *
      complementarySymbol n z lk.1 * complementarySymbol n z lk.2 * f.val lk.2‖) := by
  have hs := ((Equiv.subLeft n).prodCongr (Equiv.subLeft n)).summable_iff.mpr
    (summable_norm_weightedOffDiagonalTerm hq w d a f n z hz)
  have he (lk : ℤ × ℤ) :
      ‖weightedOffDiagonalTerm w d a f n z (n-lk.1) (n-lk.2)‖ =
      w (2*n) * ‖d.val (n+lk.1) * a.val (lk.1+lk.2) *
        complementarySymbol n z lk.1 * complementarySymbol n z lk.2 * f.val lk.2‖ := by
    unfold weightedOffDiagonalTerm
    rw [show 2*n-(n-lk.1) = n+lk.1 by ring, show n+lk.1-(n-lk.2) = lk.1+lk.2 by ring,
      sub_sub_cancel, sub_sub_cancel]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le]
    ring
  have hs' : Summable (fun lk : ℤ × ℤ => w (2*n) * ‖d.val (n+lk.1) * a.val (lk.1+lk.2) *
      complementarySymbol n z lk.1 * complementarySymbol n z lk.2 * f.val lk.2‖) := hs.congr he
  simpa only [← mul_assoc, inv_mul_cancel₀ (w.positive (2*n)).ne', one_mul] using hs'.mul_left (w (2*n))⁻¹

/-- The source physical double series has the weighted two-index Hölder bound. -/
theorem weighted_norm_tsum_offDiagonal_le [p.HolderConjugate q] (hq : 1 < q)
    (w : SpectralWeight) (d a f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w (2*n) * ‖∑' l : ℤ, ∑' k : ℤ, d.val (n+l) * a.val (l+k) *
      complementarySymbol n z l * complementarySymbol n z k * f.val k‖ ≤
      ‖d‖ * w.shiftedNorm n f * ‖doubleReciprocalRow hq (WeightedCoeff.weightEquiv w.toWeight p a) n‖ := by
  have h := norm_tsum_weightedOffDiagonalTerm_le hq w d a f n z hz
  rwa [tsum_weightedOffDiagonalTerm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le] at h

/-- A reflected negative component has exactly the shifted norm required by the source test. -/
theorem shiftedNorm_reflected_fst_le_pair (w : SpectralWeight) (n : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedNorm n (w.reflection f.fst) ≤ w.shiftedPairNorm n f := by
  rw [w.shiftedNorm_reflection, ← w.norm_modulation]
  exact WithLp.norm_fst_le _ (w.pairModulation n f)

/-- The positive component is bounded by the same exact source pair norm. -/
theorem shiftedNorm_snd_le_pair (w : SpectralWeight) (n : ℤ) (f : WeightedCoeffPair w.toWeight p) :
    w.shiftedNorm n f.snd ≤ w.shiftedPairNorm n f := by
  rw [← w.norm_modulation]
  exact WithLp.norm_snd_le _ (w.pairModulation n f)

local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The actual negative off-diagonal remainder satisfies the source weighted row estimate. -/
theorem weightedResonantBMinus_remainder_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBMinus hp w φ n z hz h - φ.fst.val (-(2*n))‖ ≤
      (2 * ‖φ.fst‖^2) * ‖doubleReciprocalRow
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
        (WeightedCoeff.weightEquiv w.toWeight p φ.snd) n‖ := by
  have ht := weighted_norm_tsum_offDiagonal_le
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) w
    (w.reflection φ.fst) φ.snd (w.reflection (weightedResonantEvenVector hp w φ n z hz h 1).fst) n z hz
  simp only [SpectralWeight.reflection_apply, LinearIsometryEquiv.norm_map] at ht
  rw [weightedResonantBMinus_remainder_eq_tsum]
  apply ht.trans
  have hu := (shiftedNorm_reflected_fst_le_pair w n (weightedResonantEvenVector hp w φ n z hz h 1)).trans
    (shiftedPairNorm_evenVector_one_le hp w φ n z hz h hh)
  calc
    _ ≤ (‖φ.fst‖ * (2 * ‖φ.fst‖)) * ‖doubleReciprocalRow _ _ n‖ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The positive remainder has the opposite weighted component norm and reflected inner potential. -/
theorem weightedResonantBPlus_remainder_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (hh : ‖weightedPotentialSquareInShift hp w φ n z hz‖ ≤ 1/2) :
    w (2*n) * ‖weightedResonantBPlus hp w φ n z hz h - φ.snd.val (2*n)‖ ≤
      (2 * ‖φ.snd‖^2) * ‖doubleReciprocalRow
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
        (WeightedCoeff.weightEquiv w.toWeight p (w.reflection φ.fst)) n‖ := by
  have ht := weighted_norm_tsum_offDiagonal_le
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) w
    φ.snd (w.reflection φ.fst) (weightedResonantEvenVector hp w φ n z hz h 0).snd n z hz
  simp only [SpectralWeight.reflection_apply] at ht
  rw [weightedResonantBPlus_remainder_eq_tsum]
  apply ht.trans
  have hu := (shiftedNorm_snd_le_pair w n (weightedResonantEvenVector hp w φ n z hz h 0)).trans
    (shiftedPairNorm_evenVector_zero_le hp w φ n z hz h hh)
  calc
    _ ≤ (‖φ.snd‖ * (2 * ‖φ.snd‖)) * ‖doubleReciprocalRow _ _ n‖ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

end NLS.ZakharovShabat
