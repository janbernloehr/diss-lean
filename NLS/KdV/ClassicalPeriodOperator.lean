import NLS.KdV.ClassicalAllContourPeriodBounds
import NLS.SequenceSpaces.ConvolutionMatrixAnalytic
import NLS.SequenceSpaces.ReciprocalSquareKernel
import NLS.SequenceSpaces.OperatorBasisExt

/-! # A constructed bounded operator for the actual infinite Hill periods

Positive input columns are numerator coefficients and positive output rows
are contour periods. Nonpositive coordinates are extended by the identity.
All matrix entries are actual integrals. No bounded matrix action is assumed.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

def positiveIntegerIndex (n : ℤ) (hn : 0 < n) : ℕ+ := ⟨n.toNat,by omega⟩

theorem positiveIntegerIndex_int (n : ℤ) (hn : 0 < n) :
    (positiveIntegerIndex n hn : ℤ) = n := Int.toNat_of_nonneg hn.le

theorem positiveIntegerIndex_real (n : ℤ) (hn : 0 < n) :
    (positiveIntegerIndex n hn : ℝ) = (n : ℝ) := by exact_mod_cast positiveIntegerIndex_int n hn

theorem positiveIntegerIndex_eq_iff (n m : ℤ) (hn : 0 < n) (hm : 0 < m) :
    positiveIntegerIndex n hn = positiveIntegerIndex m hm ↔ n = m := by
  constructor
  · intro h
    have he := congrArg (fun k : ℕ+ => (k : ℤ)) h
    simpa only [positiveIntegerIndex_int] using he
  · intro h
    subst m
    rfl

/-- Full integer-index matrix: actual positive periods and identity on
the complementary nonpositive subspace. Mixed entries are zero. -/
def classicalHillPeriodMatrix (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (m n : ℤ) : ℂ :=
  if hm : 0 < m then
    if hn : 0 < n then classicalHillUniformHighPeriod N (positiveIntegerIndex n hn)
      (positiveIntegerIndex m hm) q else 0
  else if m = n then 1 else 0

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem matrix_bound (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (m n : ℤ) :
    ‖classicalHillPeriodMatrix N q m n‖ ≤
      ((80/Real.pi)*A+1)*‖NLS.Coeff.reciprocalSquareKernel (m-n)‖ := by
  have hA := D.amplitude_pos
  have hK : 0 < (80/Real.pi)*A := by positivity
  unfold classicalHillPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn]
      have hb := D.norm_period_le (positiveIntegerIndex n hn) (positiveIntegerIndex m hm) q hq
      simp only [positiveIntegerIndex_eq_iff,positiveIntegerIndex_real] at hb
      rw [NLS.Coeff.norm_reciprocalSquareKernel_apply]
      by_cases hmn : m = n
      · subst m
        simp only [ite_true] at hb
        simpa only [ite_true,sub_self,mul_one] using hb.trans (by linarith : (80/Real.pi)*A ≤ (80/Real.pi)*A+1)
      · rw [if_neg (sub_ne_zero.mpr hmn)]
        rw [if_neg (Ne.symm hmn)] at hb
        apply hb.trans
        rw [Int.cast_sub,div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · rw [dif_neg hn,norm_zero]
      positivity
  · rw [dif_neg hm]
    by_cases hmn : m = n
    · subst n
      simp only [ite_true,norm_one,sub_self,NLS.Coeff.norm_reciprocalSquareKernel_apply,mul_one]
      linarith
    · rw [if_neg hmn,norm_zero]
      positivity

theorem matrix_free (m n : ℤ) : classicalHillPeriodMatrix N 0 m n = if m = n then 1 else 0 := by
  unfold classicalHillPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn,D.period_free]
      simp only [positiveIntegerIndex_eq_iff]
      exact if_congr eq_comm rfl rfl
    · rw [dif_neg hn,if_neg (by omega : m ≠ n)]
  · rw [dif_neg hm]

theorem matrix_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun q => classicalHillPeriodMatrix N q m n) V := by
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · simpa only [classicalHillPeriodMatrix,dif_pos hm,dif_pos hn] using
        D.period_analytic (positiveIntegerIndex n hn) (positiveIntegerIndex m hm)
    · simpa only [classicalHillPeriodMatrix,dif_pos hm,dif_neg hn] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : NLS.LinearVolterra.Curve ℂ => (0 : ℂ)) V)
  · simpa only [classicalHillPeriodMatrix,dif_neg hm] using
      (analyticOnNhd_const : AnalyticOnNhd ℂ
        (fun _ : NLS.LinearVolterra.Curve ℂ => if m = n then (1 : ℂ) else 0) V)

end ClassicalAllContourPeriodData

/-- An actual infinite period operator, analytic in the Banach operator norm,
with one common norm bound and the exact free identity. -/
theorem exists_classicalHill_analytic_period_operator :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), ∃ C : ℝ,
      ∃ T : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ 0 < C ∧
        AnalyticOnNhd ℂ T V ∧ (∀ q ∈ V, ‖T q‖ ≤ C) ∧
        (∀ q ∈ V, ∀ m n : ℤ, (T q (lp.single 2 n 1)) m = classicalHillPeriodMatrix N q m n) ∧
        (∀ m n : ℤ, AnalyticOnNhd ℂ (fun q => classicalHillPeriodMatrix N q m n) V) ∧
        T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        ∃ A : ℝ, ClassicalAllContourPeriodData N V A := by
  obtain ⟨N,V,A,hN,D⟩ := exists_classicalHill_all_contour_period_data
  let M : ℝ := (80/Real.pi)*A+1
  have hA := D.amplitude_pos
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨T,hTa,hTnorm,hTentry⟩ := NLS.Coeff.exists_analytic_operator_of_convolution_dominated_matrix
    (classicalHillPeriodMatrix N) V D.isOpen D.matrix_analytic NLS.Coeff.reciprocalSquareKernel
    NLS.Coeff.reciprocalSquareKernel_ne_zero M hM.le D.matrix_bound
  refine ⟨N,V,5*M,T,hN,D.isOpen,D.zero_mem,by positivity,hTa,?_,hTentry,D.matrix_analytic,?_,⟨A,D⟩⟩
  · intro q hq
    exact (hTnorm q hq).trans (by nlinarith [NLS.Coeff.norm_reciprocalSquareKernel_le])
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro n
  ext m
  rw [hTentry 0 D.zero_mem m n,D.matrix_free]
  simp only [ContinuousLinearMap.id_apply,lp.single_apply,Pi.single_apply]

end NLS.KdV
