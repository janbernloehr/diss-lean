import NLS.SequenceSpaces.Convolution
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Coefficient duality and convolution symmetry

The pairing of an `lp` sequence with an `l1` sequence is absolutely convergent.
Conjugate reflection of a convolution kernel gives the adjoint identity. This
is the coefficient-space duality calculation used in Proposition 1.1(iv),
printed page 27, without restricting the potential to the Hilbert exponent.
-/

noncomputable section
open scoped ENNReal ComplexConjugate

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute convergence of coefficient duality, linear in its first argument. -/
theorem summable_norm_pairing (a : Coeff p) (b : Coeff 1) :
    Summable (fun n : ℤ => ‖a n * conj (b n)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) ((lp.memℓp b).norm.summable_of_one.mul_left ‖a‖)
  simp only [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right
    (lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a n) (norm_nonneg _)

/-- Coefficient duality between a Banach sequence and an absolutely summable one. -/
def pairing (a : Coeff p) (b : Coeff 1) : ℂ := ∑' n : ℤ, a n * conj (b n)

theorem pairing_add_left (a a' : Coeff p) (b : Coeff 1) :
    pairing (a + a') b = pairing a b + pairing a' b := by
  simp only [pairing, lp.coeFn_add, Pi.add_apply, add_mul]
  exact (summable_norm_pairing a b).of_norm.tsum_add (summable_norm_pairing a' b).of_norm

omit [Fact (1 ≤ p)] in
theorem pairing_smul_left (z : ℂ) (a : Coeff p) (b : Coeff 1) :
    pairing (z • a) b = z * pairing a b := by
  simp only [pairing, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

theorem norm_pairing_le (a : Coeff p) (b : Coeff 1) : ‖pairing a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    _ ≤ ∑' n : ℤ, ‖a n * conj (b n)‖ := norm_tsum_le_tsum_norm (summable_norm_pairing a b)
    _ ≤ ∑' n : ℤ, ‖a‖ * ‖b n‖ := by
      apply (summable_norm_pairing a b).tsum_le_tsum
      · intro n
        simp only [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right
          (lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a n) (norm_nonneg _)
      · exact (lp.memℓp b).norm.summable_of_one.mul_left ‖a‖
    _ = _ := by
      have hb : (∑' n : ℤ, ‖b n‖) = ‖b‖ := by
        simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
      rw [tsum_mul_left, hb]

omit [Fact (1 ≤ p)] in
/-- Pairing two representations of the same coefficients gives their squared energy. -/
theorem pairing_self_eq (a : Coeff p) (b : Coeff 1) (hab : ∀ n : ℤ, a n = b n) :
    pairing a b = ((∑' n : ℤ, Complex.normSq (a n) : ℝ) : ℂ) := by
  simp only [pairing, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [← hab n, Complex.mul_conj]

omit [Fact (1 ≤ p)] in
/-- The squared coefficient energy is nonnegative. -/
theorem pairing_self_re_nonneg (a : Coeff p) (b : Coeff 1) (hab : ∀ n : ℤ, a n = b n) :
    0 ≤ (pairing a b).re := by
  rw [pairing_self_eq a b hab, Complex.ofReal_re]
  exact tsum_nonneg (fun _ => Complex.normSq_nonneg _)

/-- A nonzero sequence with absolutely summable coefficients has positive energy. -/
theorem pairing_self_re_pos (a : Coeff p) (b : Coeff 1) (hab : ∀ n : ℤ, a n = b n)
    (ha : a ≠ 0) : 0 < (pairing a b).re := by
  have hs := (summable_norm_pairing a b).of_norm
  simp_rw [← hab, Complex.mul_conj] at hs
  have hr := Complex.summable_ofReal.mp hs
  obtain ⟨n, hn⟩ : ∃ n : ℤ, a n ≠ 0 := by
    contrapose! ha
    apply lp.ext
    funext n
    exact ha n
  rw [pairing_self_eq a b hab, Complex.ofReal_re]
  exact hr.tsum_pos (fun _ => Complex.normSq_nonneg _) n (Complex.normSq_pos.mpr hn)

/-- Absolute convergence on the product index set justifies swapping convolution sums. -/
theorem summable_convolution_pairing (a : Coeff p) (f g : Coeff 1) :
    Summable (fun nk : ℤ × ℤ => a (nk.1 - nk.2) * f nk.2 * conj (g nk.1)) := by
  have h := ((lp.memℓp g).norm.summable_of_one.mul_of_nonneg
    (lp.memℓp f).norm.summable_of_one (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖a‖
  apply h.of_norm_bounded
  rintro ⟨n, k⟩
  simp only [norm_mul, Complex.norm_conj]
  calc
    _ ≤ ‖a‖ * ‖f k‖ * ‖g n‖ := by
      gcongr
      exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a (n-k)
    _ = _ := by ring

/-- Conjugate-reflected kernels satisfy the adjoint convolution identity. -/
theorem pairing_convolution_conj (a a' : Coeff p)
    (ha : ∀ n : ℤ, a' n = conj (a (-n))) (f g : Coeff 1) :
    pairing (convolution a f) g = conj (pairing (convolution a' g) f) := by
  simp only [pairing, convolution_apply]
  simp_rw [← tsum_mul_right, Complex.conj_tsum, map_mul]
  calc
    _ = ∑' k : ℤ, ∑' n : ℤ, a (n-k) * f k * conj (g n) :=
      (summable_convolution_pairing a f g).tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro k
      apply tsum_congr
      intro n
      rw [ha]
      simp only [neg_sub, starRingEnd_self_apply]
      ring

end NLS.Coeff
