import NLS.FunctionalAnalysis.ConjugatedSquaredNeumann

/-!
# Quantitative bounds for the transported even Neumann inverse

Bounds are measured after the chosen change of coordinates, without losses
from its norm or inverse norm. The finite-series remainder is geometric in
the norm of the conjugated square.
-/

noncomputable section
namespace NLS.SquaredNeumann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Transporting the inverse and then a vector recovers the ordinary even inverse. -/
theorem apply_conjugateEvenCorrection (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) (f : E) :
    e (conjugateEvenCorrection e K h f) =
      evenCorrection (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h) (e f) := by
  simp only [conjugateEvenCorrection, ContinuousLinearEquiv.symm_conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse bound in the chosen equivalent norm has no coordinate-change factor. -/
theorem norm_conjugateEvenCorrection_apply_le (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) (f : E) :
    ‖e (conjugateEvenCorrection e K h f)‖ ≤ (1 - ‖e.conjContinuousAlgEquiv (K^2)‖)⁻¹ * ‖e f‖ := by
  rw [apply_conjugateEvenCorrection]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [map_pow] using norm_evenCorrection_le (e.conjContinuousAlgEquiv K) (by simpa only [map_pow] using h)

/-- The source half-size contraction gives the constant two in the chosen norm. -/
theorem norm_conjugateEvenCorrection_apply_le_two (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1)
    (hh : ‖e.conjContinuousAlgEquiv (K^2)‖ ≤ 1/2) (f : E) :
    ‖e (conjugateEvenCorrection e K h f)‖ ≤ 2 * ‖e f‖ := by
  apply (norm_conjugateEvenCorrection_apply_le e K h f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sub_pos.mpr h)).mpr
  linarith

/-- The exact remainder after `m` even Neumann terms. -/
theorem conjugateEvenCorrection_sub_sum (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) (m : ℕ) :
    conjugateEvenCorrection e K h - ∑ j ∈ Finset.range m, (K^2)^j =
      (K^2)^m * conjugateEvenCorrection e K h := by
  have hs : (∑ j ∈ Finset.range m, (K^2)^j) =
      conjugateEvenCorrection e K h - (K^2)^m * conjugateEvenCorrection e K h := by
    calc
      _ = (∑ j ∈ Finset.range m, (K^2)^j) * ((1-K^2) * conjugateEvenCorrection e K h) := by
        rw [mul_conjugateEvenCorrection, mul_one]
      _ = ((∑ j ∈ Finset.range m, (K^2)^j) * (1-K^2)) * conjugateEvenCorrection e K h := (mul_assoc _ _ _).symm
      _ = _ := by rw [geom_sum_mul_neg, sub_mul, one_mul]
  rw [hs, sub_sub_cancel]

/-- Geometric remainder bound in the exact chosen norm. -/
theorem norm_conjugateEvenCorrection_sub_sum_apply_le (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) (m : ℕ) (f : E) :
    ‖e ((conjugateEvenCorrection e K h - ∑ j ∈ Finset.range m, (K^2)^j) f)‖ ≤
      (‖e.conjContinuousAlgEquiv (K^2)‖^m * (1 - ‖e.conjContinuousAlgEquiv (K^2)‖)⁻¹) * ‖e f‖ := by
  rw [conjugateEvenCorrection_sub_sum, mul_apply_eq_comp]
  have he (A : E →L[ℂ] E) (x : E) : e (A x) = e.conjContinuousAlgEquiv A (e x) := by
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [he, map_pow]
  have hpw : ‖e.conjContinuousAlgEquiv (K^2)^m‖ ≤ ‖e.conjContinuousAlgEquiv (K^2)‖^m := by
    cases m with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E))
    | succ m => exact norm_pow_le' _ (Nat.succ_pos m)
  calc
    _ ≤ ‖e.conjContinuousAlgEquiv (K^2)^m‖ * ‖e (conjugateEvenCorrection e K h f)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖e.conjContinuousAlgEquiv (K^2)‖^m * ((1-‖e.conjContinuousAlgEquiv (K^2)‖)⁻¹ * ‖e f‖) :=
      mul_le_mul hpw (norm_conjugateEvenCorrection_apply_le e K h f) (norm_nonneg _) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- Under the half-size bound the error after `m` terms is at most `2·2⁻ᵐ` times the input norm. -/
theorem norm_conjugateEvenCorrection_sub_sum_apply_le_half (e : E ≃L[ℂ] E) (K : E →L[ℂ] E)
    (h : ‖e.conjContinuousAlgEquiv (K^2)‖ < 1) (hh : ‖e.conjContinuousAlgEquiv (K^2)‖ ≤ 1/2)
    (m : ℕ) (f : E) :
    ‖e ((conjugateEvenCorrection e K h - ∑ j ∈ Finset.range m, (K^2)^j) f)‖ ≤
      (2 * (1/2 : ℝ)^m) * ‖e f‖ := by
  have hi : (1 - ‖e.conjContinuousAlgEquiv (K^2)‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sub_pos.mpr h)).mpr
    linarith
  apply (norm_conjugateEvenCorrection_sub_sum_apply_le e K h m f).trans
  calc
    _ ≤ ((1/2 : ℝ)^m * 2) * ‖e f‖ := by gcongr
    _ = _ := by rw [mul_comm ((1/2 : ℝ)^m) 2]

end NLS.SquaredNeumann
