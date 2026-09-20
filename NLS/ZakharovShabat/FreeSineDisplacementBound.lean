import NLS.ZakharovShabat.FreeSineQuotient
import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-!
# Recovering a free-disc displacement from the sine value

On any fixed free disc of radius less than pi, the filled sine quotient never
vanishes. Compactness bounds its inverse uniformly in the signed index, so
an lp estimate for sine values gives an lp estimate for displacements.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- The only sine zero in a free disc of radius less than pi is its center. -/
theorem eq_freeCenter_of_sin_eq_zero {r : ℝ} (hr : r < Real.pi) (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ r) (hs : sin z = 0) : z = (Real.pi : ℂ)*n := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  have he : z = (Real.pi : ℂ)*k := by simpa [mul_comm] using hk
  rw [he, norm_free_center_sub] at hz
  have hkn : k = n := by
    by_contra h
    have hi : (1 : ℝ) ≤ |((k-n : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    have hb := mul_le_mul_of_nonneg_left hi Real.pi_pos.le
    rw [mul_one] at hb
    linarith
  simpa only [hkn] using he

/-- The filled quotient has no zero on a free disc of radius less than pi. -/
theorem freeSineQuotient_ne_zero_on_disc {r : ℝ} (hr : r < Real.pi) (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ r) : freeSineQuotient n z ≠ 0 := by
  by_cases he : z = (Real.pi : ℂ)*n
  · subst z
    rw [freeSineQuotient_center]
    exact norm_pos_iff.mp (by rw [norm_cos_freeCenter]; norm_num)
  · rw [freeSineQuotient_eq_div n z he]
    exact div_ne_zero (fun hs => he (eq_freeCenter_of_sin_eq_zero hr n z hz hs)) (sub_ne_zero.mpr he)

/-- Inverse quotient norms are unchanged by translating back to the zero disc. -/
theorem norm_inv_freeSineQuotient_translate (n : ℤ) (z : ℂ) :
    ‖(freeSineQuotient n z)⁻¹‖ = ‖(freeSineQuotient 0 (z-(Real.pi : ℂ)*n))⁻¹‖ := by
  simp only [norm_inv, freeSineQuotient, norm_mul, norm_cos_freeCenter, one_mul,
    Int.cast_zero, mul_zero, sub_zero, cos_zero]

/-- A single finite constant bounds all inverse filled quotients on the fixed-radius free discs. -/
theorem exists_bound_inv_freeSineQuotient {r : ℝ} (hr : r < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ r → ‖(freeSineQuotient n z)⁻¹‖ ≤ C := by
  have hc : ContinuousOn (fun z => (freeSineQuotient 0 z)⁻¹) (closedBall 0 r) :=
    (continuous_freeSineQuotient 0).continuousOn.inv₀ (fun z hz =>
      freeSineQuotient_ne_zero_on_disc hr 0 z (by simpa using hz))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun n z hz => ?_⟩
  rw [norm_inv_freeSineQuotient_translate]
  exact (hC _ (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans (le_max_left _ _)

/-- Sine values control displacements uniformly throughout all free discs of a fixed radius. -/
theorem exists_freeDisc_sine_displacement_bound {r : ℝ} (hr : r < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ r →
      ‖z-(Real.pi : ℂ)*n‖ ≤ C*‖sin z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_bound_inv_freeSineQuotient hr
  refine ⟨C, hC, fun n z hz => ?_⟩
  have he : z-(Real.pi : ℂ)*n = (freeSineQuotient n z)⁻¹*sin z := by
    rw [← freeSineQuotient_mul_sub n z, ← mul_assoc,
      inv_mul_cancel₀ (freeSineQuotient_ne_zero_on_disc hr n z hz), one_mul]
  calc
    _ = ‖(freeSineQuotient n z)⁻¹‖*‖sin z‖ := by rw [← norm_mul, ← he]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb n z hz) (norm_nonneg _)

end NLS.ZakharovShabat
