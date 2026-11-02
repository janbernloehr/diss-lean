import NLS.KdV.HillHminusOnePeriodBounds
import NLS.KdV.ClassicalPeriodOperator
import NLS.ComplexAnalysis.AnalyticOperatorInverse

/-! # The actual rough Hill period operator and its analytic inverse -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

/-- Full integer-index matrix: actual positive periods and identity on
the complementary nonpositive subspace. Mixed entries are zero. -/
def hillHminusPeriodMatrix (C : HillHminusMiuraChart) (N : ℕ) (q : PeriodOneHminusOne) (m n : ℤ) : ℂ :=
  if hm : 0 < m then
    if hn : 0 < n then hillHminusPeriodEntry C N (positiveIntegerIndex n hn)
      (positiveIntegerIndex m hm) q else 0
  else if m = n then 1 else 0

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set (PeriodOneHminusOne)} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem matrix_bound (q : PeriodOneHminusOne) (hq : q ∈ V) (m n : ℤ) :
    ‖hillHminusPeriodMatrix C N q m n‖ ≤
      ((80/Real.pi)*A+1)*‖NLS.Coeff.reciprocalSquareKernel (m-n)‖ := by
  have hA := D.amplitude_pos
  have hK : 0 < (80/Real.pi)*A := by positivity
  unfold hillHminusPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn]
      have hb := D.norm_period_le (positiveIntegerIndex n hn) (positiveIntegerIndex m hm) q hq
      simp only [positiveIntegerIndex_eq_iff,positiveIntegerIndex_real] at hb
      rw [NLS.Coeff.norm_reciprocalSquareKernel_apply]
      by_cases hmn : m = n
      · subst m
        simp only [ite_true,mul_one] at hb
        simpa only [ite_true,sub_self,mul_one] using hb.trans (by linarith : (80/Real.pi)*A ≤ (80/Real.pi)*A+1)
      · rw [if_neg (sub_ne_zero.mpr hmn)]
        rw [if_neg (Ne.symm hmn)] at hb
        apply hb.trans
        rw [Int.cast_sub,div_eq_mul_inv,inv_pow]
        exact mul_le_mul_of_nonneg_right
          (show (80/Real.pi)*A ≤ (80/Real.pi)*A+1 by linarith) (by positivity)
    · rw [dif_neg hn,norm_zero]
      positivity
  · rw [dif_neg hm]
    by_cases hmn : m = n
    · subst n
      simp only [ite_true,norm_one,sub_self,NLS.Coeff.norm_reciprocalSquareKernel_apply,mul_one]
      linarith
    · rw [if_neg hmn,norm_zero]
      positivity

theorem matrix_free (m n : ℤ) : hillHminusPeriodMatrix C N 0 m n = if m = n then 1 else 0 := by
  unfold hillHminusPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn,D.period_free]
      simp only [positiveIntegerIndex_eq_iff]
      exact if_congr eq_comm rfl rfl
    · rw [dif_neg hn,if_neg (by omega : m ≠ n)]
  · rw [dif_neg hm]

theorem matrix_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun q => hillHminusPeriodMatrix C N q m n) V := by
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · simpa only [hillHminusPeriodMatrix,dif_pos hm,dif_pos hn] using
        D.period_analytic (positiveIntegerIndex n hn) (positiveIntegerIndex m hm)
    · simpa only [hillHminusPeriodMatrix,dif_pos hm,dif_neg hn] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : PeriodOneHminusOne => (0 : ℂ)) V)
  · simpa only [hillHminusPeriodMatrix,dif_neg hm] using
      (analyticOnNhd_const : AnalyticOnNhd ℂ
        (fun _ : PeriodOneHminusOne => if m = n then (1 : ℂ) else 0) V)

end HillHminusUniformPeriodData

/-- Constructed from the literal rough period entries, with an actual two-sided
analytic inverse on one Hminus1-open neighborhood of zero. -/
theorem exists_hillHminus_analytic_period_inverse :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      ∃ T R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ T V ∧ AnalyticOnNhd ℂ R V ∧
        T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ q ∈ V, (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          (R q).comp (T q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ ‖R q‖ ≤ 2) ∧
        (∀ q ∈ V, ∀ m n : ℤ, (T q (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,W,A,hN,D⟩ := exists_hillHminus_uniform_period_data
  let M : ℝ := (80/Real.pi)*A+1
  have hA := D.amplitude_pos
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨T,hTa,_,hTentry⟩ := NLS.Coeff.exists_analytic_operator_of_convolution_dominated_matrix
    (hillHminusPeriodMatrix C N) W D.isOpen D.matrix_analytic NLS.Coeff.reciprocalSquareKernel
    NLS.Coeff.reciprocalSquareKernel_ne_zero M hM.le D.matrix_bound
  have hT0 : T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
    apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro n
    ext m
    rw [hTentry 0 D.zero_mem m n,D.matrix_free]
    simp only [ContinuousLinearMap.id_apply,lp.single_apply,Pi.single_apply]
  obtain ⟨V,R,hVW,hV,h0V,hRa,hR0,hInv⟩ :=
    NLS.ComplexAnalysis.exists_analytic_operator_inverse_near_zero T W D.isOpen D.zero_mem hTa hT0
  exact ⟨C,N,V,T,R,hN,hV,h0V,hTa.mono hVW,hRa,hT0,hR0,hInv,
    fun q hq m n => hTentry q (hVW hq) m n,A,D.mono hVW hV h0V⟩

end NLS.KdV
