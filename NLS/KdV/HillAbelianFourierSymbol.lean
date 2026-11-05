import NLS.KdV.HillNativePositiveAbelianCoordinates
import NLS.SequenceSpaces.DeletedDiagonal

/-! # The exact weighted Fourier derivative is a mean-zero Hilbert isomorphism -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.KdV

private theorem normalized_fourier_symbol_bounds (t : ℝ) (ht : 1 ≤ t) :
    1/4 ≤ ‖(Real.sqrt (1+t) : ℂ)/(Real.sqrt (2*t*Real.pi) : ℂ)‖ ∧
      ‖(Real.sqrt (1+t) : ℂ)/(Real.sqrt (2*t*Real.pi) : ℂ)‖ ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have hA : 0 ≤ Real.sqrt (1+t) := Real.sqrt_nonneg _
  have hB : 0 < Real.sqrt (2*t*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hAsq := Real.sq_sqrt (by positivity : 0 ≤ 1+t)
  have hBsq := Real.sq_sqrt (by positivity : 0 ≤ 2*t*Real.pi)
  have hpiLo := mul_le_mul_of_nonneg_right Real.pi_gt_three.le ht0.le
  have hpiHi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le ht0.le
  have hAB : Real.sqrt (1+t) ≤ Real.sqrt (2*t*Real.pi) := by
    apply (sq_le_sq₀ hA hB.le).mp
    rw [hAsq,hBsq]
    nlinarith
  have hBA : Real.sqrt (2*t*Real.pi) ≤ 4*Real.sqrt (1+t) := by
    apply (sq_le_sq₀ hB.le (by positivity : 0 ≤ 4*Real.sqrt (1+t))).mp
    rw [mul_pow,hAsq,hBsq]
    nlinarith
  rw [norm_div,norm_real,norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hA,abs_of_pos hB]
  exact ⟨(le_div_iff₀ hB).mpr (by linarith),(div_le_one hB).mpr hAB⟩

def hillAbelianFourierSymbol : Coeff ⊤ :=
  ⟨fun j => if j = 0 then 0 else (Real.sqrt (1+(j.natAbs : ℝ)) : ℂ)/(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ), by
    apply memℓp_infty
    refine ⟨1,?_⟩
    rintro _ ⟨j,rfl⟩
    change ‖if j = 0 then (0 : ℂ) else (Real.sqrt (1+(j.natAbs : ℝ)) : ℂ)/(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)‖ ≤ 1
    by_cases hj : j = 0
    · simp only [if_pos hj,norm_zero,zero_le_one]
    · rw [if_neg hj]
      exact (normalized_fourier_symbol_bounds _ (by exact_mod_cast (Int.natAbs_pos.mpr hj))).2⟩

theorem hillAbelianFourierSymbol_lower (j : ℤ) (hj : j ≠ 0) : 1/4 ≤ ‖hillAbelianFourierSymbol j‖ := by
  change 1/4 ≤ ‖if j = 0 then (0 : ℂ) else _‖
  rw [if_neg hj]
  exact (normalized_fourier_symbol_bounds _ (by exact_mod_cast (Int.natAbs_pos.mpr hj))).1

theorem hillAbelianFourierSymbol_apply (j : ℤ) : hillAbelianFourierSymbol j =
    (hillAbelianTargetWeight SpectralWeight.one j : ℂ)*(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹ := by
  have ht : |(j : ℝ)| = (j.natAbs : ℝ) := by simp only [Nat.cast_natAbs,Int.cast_abs]
  rw [hillAbelianTargetWeight_one_sqrt,ht]
  by_cases hj : j = 0
  · subst j
    simp only [hillAbelianFourierSymbol,if_true,Int.natAbs_zero,Nat.cast_zero,mul_zero,zero_mul,
      Real.sqrt_zero,ofReal_zero,inv_zero,mul_zero]
  · change (if j = 0 then (0 : ℂ) else _) = _
    rw [if_neg hj,div_eq_mul_inv]

def hillAbelianWeightedFourierEquiv : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0 :=
  Coeff.deletedMultiplierEquivOfLowerBound 0 hillAbelianFourierSymbol (1/4) (by norm_num)
    hillAbelianFourierSymbol_lower

theorem hillAbelianWeightedFourierEquiv_apply (h : DeletedCoeff 2 0) (j : ℤ) :
    (hillAbelianWeightedFourierEquiv h).val j =
      (hillAbelianTargetWeight SpectralWeight.one j : ℂ)*
        ((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) := by
  change hillAbelianFourierSymbol j*h.val j = _
  rw [hillAbelianFourierSymbol_apply,mul_assoc]

end NLS.KdV
