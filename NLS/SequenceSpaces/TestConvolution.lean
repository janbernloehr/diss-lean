import NLS.SequenceSpaces.TestDuality
import NLS.SequenceSpaces.Reflection

/-!
# Transposing convolution onto complex-linear tests

The reflected multiplier acts on the `ℓ¹` test sequence. Absolute convergence
on the product lattice justifies both changes of order; no finite-support
assumption is imposed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute convergence of the bilinear convolution/test sum. -/
theorem summable_convolution_test (a : Coeff p) (b c : Coeff 1) :
    Summable (fun nk : ℤ × ℤ => a (nk.1 - nk.2) * b nk.2 * c nk.1) := by
  have h := ((lp.memℓp c).norm.summable_of_one.mul_of_nonneg
    (lp.memℓp b).norm.summable_of_one (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖a‖
  apply h.of_norm_bounded
  rintro ⟨n, k⟩
  simp only [norm_mul]
  calc
    _ ≤ ‖a‖ * ‖b k‖ * ‖c n‖ := by
      gcongr
      exact lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a (n-k)
    _ = _ := by ring

/-- Reflected convolution is the test-side sum with the opposite frequency shift. -/
theorem convolution_reflection_apply (b c : Coeff 1) (n : ℤ) :
    convolution c (reflection b) n = ∑' k : ℤ, b k * c (n + k) := by
  rw [convolution_apply, ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => c (n - k) * reflection b k)]
  simp only [Equiv.neg_apply, reflection_apply, neg_neg, sub_neg_eq_add]
  exact tsum_congr (fun k => mul_comm _ _)

/-- Convolution transposes to reflected convolution on the test sequence. -/
theorem testPairing_convolution (a : Coeff p) (b c : Coeff 1) :
    testPairing (convolution a b) c = testPairing a (convolution c (reflection b)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun nk => (nk.1 + nk.2, nk.2)
      invFun := fun nk => (nk.1 - nk.2, nk.2)
      left_inv := by intro nk; ext <;> simp
      right_inv := by intro nk; ext <;> simp }
  have hs := summable_convolution_test a b c
  have hs' : Summable (fun nk : ℤ × ℤ => a nk.1 * b nk.2 * c (nk.1 + nk.2)) := by
    have h := e.summable_iff.mpr hs
    change Summable (fun nk : ℤ × ℤ => a ((nk.1 + nk.2) - nk.2) * b nk.2 * c (nk.1 + nk.2)) at h
    simpa only [add_sub_cancel_right] using h
  simp only [testPairing, convolution_apply]
  simp_rw [← tsum_mul_right]
  calc
    _ = ∑' k : ℤ, ∑' n : ℤ, a (n-k) * b k * c n := hs.tsum_comm.symm
    _ = ∑' k : ℤ, ∑' n : ℤ, a n * b k * c (n+k) := by
      apply tsum_congr
      intro k
      have h := ((Equiv.addRight k).tsum_eq (fun n : ℤ => a (n-k) * b k * c n)).symm
      change (∑' n : ℤ, a (n-k) * b k * c n) =
        ∑' n : ℤ, a ((n+k)-k) * b k * c (n+k) at h
      simpa only [add_sub_cancel_right] using h
    _ = ∑' n : ℤ, ∑' k : ℤ, a n * b k * c (n+k) := hs'.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← convolution_apply, convolution_reflection_apply, ← tsum_mul_left]
      exact tsum_congr (fun k => mul_assoc _ _ _)

end NLS.Coeff
