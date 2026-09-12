import NLS.SequenceSpaces.WeightedSandwich
import NLS.SequenceSpaces.SandwichMajorant

/-!
# Weight gains for two truncated reciprocal multipliers

A pointwise gain in the weights on the two finite windows passes to the exact
shifted `ℓ¹` output norm. Positive coefficient majorants connect the proof to
the existing unweighted Hölder–Young sandwich, retaining its constant one.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- A gain on the two near windows transfers to the whole weighted sandwich. -/
theorem shiftedNorm_sandwich_truncate_le_gain (w : SpectralWeight) (a : Coeff q)
    (φ : WeightedCoeff w.toWeight p) (b : Coeff q) (A B : Finset ℤ) (i : ℤ)
    {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ j ∈ A, ∀ k ∈ B, w (j+i) ≤ C * w (j-k) * w (k+i))
    (f : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (w.sandwich (Coeff.truncate A a) φ (Coeff.truncate B b) f) ≤
      (C * ‖a‖ * ‖φ‖ * ‖b‖) * w.shiftedNorm i f := by
  let a' := Coeff.truncate A a
  let b' := Coeff.truncate B b
  let φW := WeightedCoeff.weightEquiv w.toWeight p φ
  let fW := WeightedCoeff.weightEquiv (w.toWeight.shift i) p (w.toShift i f)
  let u := Coeff.convolutionSandwich (Coeff.magnitude a') (Coeff.magnitude φW)
    (Coeff.magnitude b') (Coeff.magnitude fW)
  let v := WeightedCoeff.weightEquiv (w.toWeight.shift i) 1
    (w.toShift i (w.sandwich a' φ b' f))
  have hφ (k : ℤ) : ‖φW k‖ = w k * ‖φ.val k‖ := by
    simp only [φW, WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (w.positive k)]
  have hf (k : ℤ) : ‖fW k‖ = w (k+i) * ‖f.val k‖ := by
    simp only [fW, WeightedCoeff.weightEquiv_apply, toShift_apply, Weight.shift_apply,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive (k+i))]
  have hb (k : ℤ) (hk : k ∉ B) : b' k = 0 := by simp [b', hk]
  have hv (j : ℤ) : ‖v j‖ = w (j+i) * ‖a' j * ∑' k : ℤ, φ.val (j-k) * (b' k * f.val k)‖ := by
    simp only [v, WeightedCoeff.weightEquiv_apply, toShift_apply, sandwich_apply,
      Weight.shift_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.positive (j+i))]
  have hu (j : ℤ) : ‖u j‖ = ‖a' j‖ * ∑' k : ℤ, ‖φW (j-k)‖ * (‖b' k‖ * ‖fW k‖) :=
    Coeff.norm_magnitude_sandwich_apply a' φW b' fW j
  have hdom (j : ℤ) : ‖v j‖ ≤ C * ‖u j‖ := by
    rw [hv, hu]
    by_cases hj : j ∈ A
    · have hs : Summable (fun k : ℤ => ‖φ.val (j-k) * (b' k * f.val k)‖) :=
        summable_of_ne_finset_zero (s := B) (by intro k hk; simp [hb k hk])
      have ht : Summable (fun k : ℤ => ‖φW (j-k)‖ * (‖b' k‖ * ‖fW k‖)) :=
        summable_of_ne_finset_zero (s := B) (by intro k hk; simp [hb k hk])
      have hrow : (∑' k : ℤ, w (j+i) * ‖φ.val (j-k) * (b' k * f.val k)‖) ≤
          ∑' k : ℤ, C * (‖φW (j-k)‖ * (‖b' k‖ * ‖fW k‖)) := by
        apply Summable.tsum_le_tsum _ (hs.mul_left _) (ht.mul_left _)
        intro k
        by_cases hk : k ∈ B
        · rw [hφ, hf, norm_mul, norm_mul]
          convert mul_le_mul_of_nonneg_right (hw j hj k hk)
            (mul_nonneg (norm_nonneg (φ.val (j-k))) (mul_nonneg (norm_nonneg (b' k)) (norm_nonneg (f.val k)))) using 1
          ring
        · simp [hb k hk]
      calc
        _ ≤ w (j+i) * (‖a' j‖ * ∑' k : ℤ, ‖φ.val (j-k) * (b' k * f.val k)‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (norm_tsum_le_tsum_norm hs) (norm_nonneg _)) (w.positive _).le
        _ = ‖a' j‖ * ∑' k : ℤ, w (j+i) * ‖φ.val (j-k) * (b' k * f.val k)‖ := by rw [tsum_mul_left]; ring
        _ ≤ ‖a' j‖ * ∑' k : ℤ, C * (‖φW (j-k)‖ * (‖b' k‖ * ‖fW k‖)) := mul_le_mul_of_nonneg_left hrow (norm_nonneg _)
        _ = _ := by rw [tsum_mul_left]; ring
    · have ha : a' j = 0 := by simp [a', Coeff.truncate_apply, hj]
      simp [ha]
  have hnorm : ‖v‖ ≤ C * ‖u‖ := by
    calc
      _ ≤ ‖(C : ℂ) • u‖ := by
        apply lp.norm_mono (by simp : (1 : ℝ≥0∞) ≠ 0)
        intro j
        simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using hdom j
      _ = _ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  have huN : ‖u‖ ≤ ‖a‖ * ‖φ‖ * ‖b‖ * w.shiftedNorm i f := by
    have h := Coeff.norm_magnitude_sandwich_le a' φW b' fW
    change ‖u‖ ≤ ‖a'‖ * ‖φ‖ * ‖b'‖ * w.shiftedNorm i f at h
    apply h.trans
    have hf0 : 0 ≤ w.shiftedNorm i f := norm_nonneg _
    gcongr
    · exact Coeff.norm_truncate_le hq0 A a
    · exact Coeff.norm_truncate_le hq0 B b
  calc
    _ ≤ C * ‖u‖ := hnorm
    _ ≤ C * (‖a‖ * ‖φ‖ * ‖b‖ * w.shiftedNorm i f) := mul_le_mul_of_nonneg_left huN hC
    _ = _ := by ring

end NLS.SpectralWeight
