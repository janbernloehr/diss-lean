import NLS.ZakharovShabat.LinearWeightKernel
import NLS.SequenceSpaces.LinearSpectralWeight
import NLS.SequenceSpaces.ShiftedWeight
import NLS.SequenceSpaces.ConjugateDuality

/-! # The inverse-bracket gain for the actual diagonal row in Lemma 25.3 -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The two opposite centers and the π/2 denominator give the diagonal gain. -/
theorem bracket_mul_complementarySymbol_le {n : ℤ} {z : ℂ}
    (hz : z ∈ resonantStrip n) (m : ℤ) :
    (1+|(n:ℝ)|)*‖complementarySymbol n z m‖ ≤ (1+|((m+n:ℤ):ℝ)|)^2 := by
  by_cases hm : m = n
  · simp [hm]; positivity
  let a : ℝ := 1+|((m+n:ℤ):ℝ)|
  let b : ℝ := |((m-n:ℤ):ℝ)|
  have ha : 1 ≤ a := by dsimp [a]; linarith [abs_nonneg ((m+n:ℤ):ℝ)]
  have hb : 1 ≤ b := by dsimp [b]; exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  have ht : 2*|(n:ℝ)| ≤ (a-1)+b := by
    have h := abs_sub (m+n:ℝ) (m-n:ℝ)
    norm_num [show (m+n:ℝ)-(m-n)=2*n by ring, abs_mul] at h
    simpa only [a,b,Int.cast_add,Int.cast_sub,add_sub_cancel_left] using h
  have hd := resonantStrip_denominator_lower_pi hz hm
  change Real.pi/2*b ≤ _ at hd
  have hd' : (3/2:ℝ)*b ≤ ‖z-(Real.pi:ℂ)*m‖ := by nlinarith [Real.pi_gt_three]
  have hgeom : 1+|(n:ℝ)| ≤ a^2*((3/2:ℝ)*b) := by
    have ha2 : a ≤ a^2 := by nlinarith
    have hab : a ≤ a^2*b := le_trans ha2 (le_mul_of_one_le_right (sq_nonneg a) hb)
    have hb' : b ≤ a^2*b := by nlinarith [mul_le_mul_of_nonneg_right ha2 (by linarith : 0 ≤ b), mul_le_mul_of_nonneg_right ha (by linarith : 0 ≤ b)]
    nlinarith
  have hd0 : 0 < ‖z-(Real.pi:ℂ)*m‖ := lt_of_lt_of_le zero_lt_one (resonantStrip_denominator_one_le hz hm)
  simp only [complementarySymbol, if_neg hm, norm_inv, ← div_eq_mul_inv]
  apply (div_le_iff₀ hd0).mpr
  exact hgeom.trans (mul_le_mul_of_nonneg_left hd' (sq_nonneg a))

/-- A weight in M₁ dominates the bracket factor required by the diagonal row. -/
theorem weight_mul_complementarySymbol_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (k : ℤ) :
    (1+|(n:ℝ)|)*‖complementarySymbol n z (-k)‖ ≤ w (n-k)^2 := by
  have h := bracket_mul_complementarySymbol_le hz (-k)
  rw [show -k+n=n-k by omega] at h
  exact h.trans (pow_le_pow_left₀ (by positivity) (SpectralWeight.bracket_le_of_hasLinearFactor hw (n-k)) 2)

/-- Cauchy–Schwarz with the actual reciprocal and the correct shifted input.
The statement includes absolute convergence of the diagonal series. -/
theorem summable_and_diagonalRow_linear (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a f : WeightedCoeff w.toWeight 2) {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) :
    (Summable (fun k : ℤ => ‖a.val (n-k)*complementarySymbol n z (-k)*f.val k‖)) ∧
    ‖∑' k : ℤ, a.val (n-k)*complementarySymbol n z (-k)*f.val k‖ ≤
      (1/(1+|(n:ℝ)|))*‖a‖*w.shiftedNorm (-n) f := by
  let A := Coeff.reindex (Equiv.subLeft n) (WeightedCoeff.weightEquiv w.toWeight 2 a)
  let F := WeightedCoeff.weightEquiv (w.toWeight.shift (-n)) 2 (w.toShift (-n) f)
  have hA (k : ℤ) : ‖A k‖ = w (n-k)*‖a.val (n-k)‖ := by
    simp only [A, Coeff.reindex_apply, Equiv.subLeft_apply, WeightedCoeff.weightEquiv_apply,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive _)]
  have hF (k : ℤ) : ‖F k‖ = w (n-k)*‖f.val k‖ := by
    have he : w (k-n) = w (n-k) := by rw [show k-n=-(n-k) by omega, w.apply_neg]
    simp only [F, WeightedCoeff.weightEquiv_apply, SpectralWeight.toShift_apply, Weight.shift_apply,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive _), ← sub_eq_add_neg, he]
  have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2) Real.HolderConjugate.two_two A F
  have hdom (k : ℤ) : ‖a.val (n-k)*complementarySymbol n z (-k)*f.val k‖ ≤
      (1/(1+|(n:ℝ)|))*(‖A k‖*‖F k‖) := by
    rw [hA,hF]
    have hh := mul_le_mul_of_nonneg_right (weight_mul_complementarySymbol_le w hw hz k)
      (mul_nonneg (norm_nonneg (a.val (n-k))) (norm_nonneg (f.val k)))
    simp only [norm_mul]
    rw [one_div, ← div_eq_inv_mul]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom (h.1.mul_left _)
  refine ⟨hs, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' k : ℤ, (1/(1+|(n:ℝ)|))*(‖A k‖*‖F k‖) :=
      Summable.tsum_le_tsum hdom hs (h.1.mul_left _)
    _ = (1/(1+|(n:ℝ)|))*(∑' k : ℤ, ‖A k‖*‖F k‖) := tsum_mul_left
    _ ≤ (1/(1+|(n:ℝ)|))*(‖A‖*‖F‖) := mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = _ := by rw [show ‖A‖=‖a‖ from Coeff.norm_reindex _ _, mul_assoc]; rfl

end NLS.ZakharovShabat
