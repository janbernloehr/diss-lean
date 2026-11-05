import NLS.ZakharovShabat.SourceDiagonalActionRootSequence

/-! # Bounded inverse physical scaling on the positive real diagonal

The common positive lower bound for the scaled action ratios bounds the
inverse of every half-order action root. The actual inverse symbol is
therefore a bounded sequence, including at arbitrarily many closed gaps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_diagonalActionRoot_scaled_inverse_bound (φ : realDiagonalSourceLocus 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, 0 < n →
      ‖((Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val)⁻¹‖ ≤ C := by
  obtain ⟨c,hc,hbase⟩ := exists_diagonalActionRatio_scaled_re_lower_bound φ
  refine ⟨(Real.sqrt c)⁻¹,by positivity,?_⟩
  intro n hn
  let z := (Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val
  have hw : Weight.sobolev (1/2) n = Real.sqrt (1+|(n : ℝ)|) := by
    rw [Weight.sobolev_apply,Real.sqrt_eq_rpow]
  have hs := congrArg norm (sourceDiagonalActionRoot_sq (by simp) (by norm_num) n φ.val)
  rw [norm_pow] at hs
  have hz : ‖z‖^2 = (1+|(n : ℝ)|)*‖sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val‖ := by
    dsimp only [z]
    rw [norm_mul,Complex.norm_of_nonneg ((Weight.sobolev (1/2)).positive n).le,mul_pow,hw,
      Real.sq_sqrt (by positivity),hs]
  have hb : c ≤ ‖z‖^2 := by
    rw [hz]
    calc
      c ≤ (1+|(n : ℝ)|)*(sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re := by
        simpa only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using hbase n hn
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)
  have hl : Real.sqrt c ≤ ‖z‖ := (sq_le_sq₀ (Real.sqrt_nonneg c) (norm_nonneg z)).mp
    (by rw [Real.sq_sqrt hc.le]; exact hb)
  rw [show ((Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val)⁻¹ = z⁻¹ from rfl,
    norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hc) hl

def sourceDiagonalActionRootInverseSequence (ψ : CoeffPair 2) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (fun n => if 0 < n then
    ((Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n ψ)⁻¹ else 0)

/-- All raw inverse-symbol entries are actual inverses on every physical
diagonal, and zero only at the unused nonpositive indices. -/
theorem sourceDiagonalActionRootInverseSequence_apply (φ : realDiagonalSourceLocus 2) (n : ℤ) :
    sourceDiagonalActionRootInverseSequence φ.val n = if 0 < n then
      ((Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val)⁻¹ else 0 := by
  obtain ⟨C,hC,hbound⟩ := exists_diagonalActionRoot_scaled_inverse_bound φ
  apply Coeff.ofFunctionOrZero_apply_of_mem
  apply memℓp_infty
  refine ⟨C,?_⟩
  rintro _ ⟨k,rfl⟩
  change ‖(if 0 < k then
    ((Weight.sobolev (1/2) k : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) k φ.val)⁻¹ else 0)‖ ≤ C
  split_ifs with hk
  · exact hbound k hk
  · simpa only [norm_zero] using hC

theorem sourceDiagonalActionRootInverseSequence_mul (φ : realDiagonalSourceLocus 2) (n : ℤ) (hn : 0 < n) :
    sourceDiagonalActionRootInverseSequence φ.val n *
      ((Weight.sobolev (1/2) n : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val) = 1 := by
  have hr : sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val ≠ 0 := by
    intro h
    have hp := (sourceDiagonalActionRoot_real_positive (by simp) (by norm_num) φ n hn).2
    rw [h,zero_re] at hp
    exact (lt_irrefl 0 hp)
  rw [sourceDiagonalActionRootInverseSequence_apply,if_pos hn]
  exact inv_mul_cancel₀ (mul_ne_zero ((Weight.sobolev (1/2)).complex_ne_zero n) hr)

end NLS.ZakharovShabat
