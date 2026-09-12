import NLS.SequenceSpaces.Embedding

/-!
# The `ℓ4 × ℓ4 → ℓ2` product

Hölder gives the product estimate used with the discrete Cotlar identity.
The square product has exactly the square of the original `ℓ4` norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : ENNReal.HolderTriple 4 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

private theorem norm_complex_mul_le : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ (1 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using ContinuousLinearMap.opNorm_mul_apply_le ℂ ℂ x

/-- Pointwise multiplication of two quartic-summable sequences. -/
def quarticProduct : Coeff 4 →L[ℂ] Coeff 4 →L[ℂ] Coeff 2 :=
  lp.holderL (p := 4) (q := 4) 2 (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (K := 1) (fun _ => norm_complex_mul_le)

@[simp] theorem quarticProduct_apply (a b : Coeff 4) (n : ℤ) :
    quarticProduct a b n = a n * b n := rfl

theorem norm_quarticProduct_le (a b : Coeff 4) : ‖quarticProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hn : ‖quarticProduct‖ ≤ 1 :=
    lp.norm_holderL_le 2 (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
      (K := 1) (fun _ => norm_complex_mul_le)
  exact (quarticProduct a).le_of_opNorm_le (by simpa using quarticProduct.le_of_opNorm_le hn a) b

/-- The square product converts the quartic norm to the Hilbert norm without loss. -/
theorem norm_quarticProduct_self (a : Coeff 4) : ‖quarticProduct a a‖ = ‖a‖ ^ 2 := by
  have h2 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (quarticProduct a a)
  have h4 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (4 : ℝ≥0∞).toReal) a
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, quarticProduct_apply, norm_mul] at h2
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at h4
  have he : (∑' n : ℤ, (‖a n‖ * ‖a n‖)^2) = ∑' n : ℤ, ‖a n‖^4 := by
    apply tsum_congr
    intro n
    ring
  rw [he, ← h4] at h2
  nlinarith [norm_nonneg (quarticProduct a a), sq_nonneg ‖a‖]

end NLS.Coeff
