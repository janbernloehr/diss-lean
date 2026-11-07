import NLS.SequenceSpaces.PositiveDiagonalEquiv

/-! The inverse of an actual positive diagonal has the reciprocal
lower-bound norm estimate on the original full l2 space. -/
noncomputable section
open Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem norm_positive_diagonal_inverse_le
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ m : ℕ+, δ ≤ ‖T (lp.single 2 m 1) m‖)
    (e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hinv : ∀ a m, e.symm a m = (T (lp.single 2 m 1) m)⁻¹*a m) :
    ‖e.symm.toContinuousLinearMap‖ ≤ δ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hδ.le)
  intro a
  change ‖e.symm a‖ ≤ δ⁻¹*‖a‖
  have hpoint (m : ℕ+) : ‖e.symm a m‖ ≤ ‖(((δ⁻¹:ℝ):ℂ) • a) m‖ := by
    rw [hinv]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,norm_inv,
      Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (hδ.trans_le (hlower m)) hδ).2 (hlower m)) (norm_nonneg _)
  have hn : ‖e.symm a‖ ≤ ‖(((δ⁻¹:ℝ):ℂ) • a)‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    exact hpoint
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)] using hn

end NLS.LpSequence
