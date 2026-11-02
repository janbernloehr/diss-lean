import NLS.KdV.ClassicalPeriodOperator
import NLS.SequenceSpaces.PositiveIndexWeight

/-! # The actual Hill period matrix with one positive-index weight

The sharper period estimate retains n*k/(k^2-n^2)^2. Conjugating the
positive block by the index weight still gives a summable reciprocal-square
majorant. This constructs a genuine operator on the weighted coefficients.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

def classicalHillWeightedPeriodMatrix (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ)
    (m n : ℤ) : ℂ :=
  (NLS.Coeff.positiveIndexWeight m/NLS.Coeff.positiveIndexWeight n)*
    classicalHillPeriodMatrix N q m n

private theorem weighted_squared_energy_kernel_le (n k : ℕ+) (hnk : n ≠ k) :
    ((k : ℝ)/(n : ℝ))*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) ≤
      1/|(k : ℝ)-(n : ℝ)|^2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hkn : (k : ℝ)-(n : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have he' : ((k : ℕ) : ℝ) = ((n : ℕ) : ℝ) := he
    exact hnk (Subtype.ext (Nat.cast_injective he'.symm))
  have hsum : (k : ℝ)+(n : ℝ) ≠ 0 := by positivity
  have hd : (k : ℝ)^2-(n : ℝ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hsum hkn
  have hrat : (k : ℝ)/((k : ℝ)+(n : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hr0 : 0 ≤ (k : ℝ)/((k : ℝ)+(n : ℝ)) := by positivity
  have hs : ((k : ℝ)/((k : ℝ)+(n : ℝ)))^2 ≤ 1 := by nlinarith
  calc
    _ = ((k : ℝ)/((k : ℝ)+(n : ℝ)))^2/|(k : ℝ)-(n : ℝ)|^2 := by
      simp only [sq_abs]
      field_simp
      ring
    _ ≤ 1/|(k : ℝ)-(n : ℝ)|^2 := div_le_div_of_nonneg_right hs (sq_nonneg _)

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem norm_weighted_offDiagonal_period_le (n k : ℕ+) (hnk : n ≠ k)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ((k : ℝ)/(n : ℝ))*‖classicalHillUniformHighPeriod N n k q‖ ≤
      ((20/Real.pi)*A)/|(k : ℝ)-(n : ℝ)|^2 := by
  have hb := norm_classicalHillUniformHighPeriod_le N n k hnk q (I*(k : ℂ)*Real.pi) A
    D.amplitude_pos.le (D.numerator_factor n q hq) (D.cover k q hq)
    (D.offDiagonal_separation n k hnk q hq) (D.primitive_bound k q hq)
  have hraw : ‖classicalHillUniformHighPeriod N n k q‖ ≤
      ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
    convert hb using 1
    ring
  have hA := D.amplitude_pos
  calc
    _ ≤ ((k : ℝ)/(n : ℝ))*(((20/Real.pi)*A)*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = ((20/Real.pi)*A)*(((k : ℝ)/(n : ℝ))*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) := by ring
    _ ≤ ((20/Real.pi)*A)*(1/|(k : ℝ)-(n : ℝ)|^2) :=
      mul_le_mul_of_nonneg_left (weighted_squared_energy_kernel_le n k hnk) (by positivity)
    _ = _ := by ring

theorem weightedMatrix_bound (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (m n : ℤ) :
    ‖classicalHillWeightedPeriodMatrix N q m n‖ ≤
      ((80/Real.pi)*A+1)*‖NLS.Coeff.reciprocalSquareKernel (m-n)‖ := by
  have hA := D.amplitude_pos
  have hK : 0 < (80/Real.pi)*A := by positivity
  unfold classicalHillWeightedPeriodMatrix classicalHillPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn]
      simp only [NLS.Coeff.positiveIndexWeight,if_pos hm,if_pos hn,norm_mul,norm_div,
        Complex.norm_intCast,abs_of_pos (by exact_mod_cast hm : (0 : ℝ) < m),
        abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
      rw [NLS.Coeff.norm_reciprocalSquareKernel_apply]
      by_cases hmn : m = n
      · subst m
        rw [div_self (by exact_mod_cast (ne_of_gt hn) : (n : ℝ) ≠ 0),one_mul,
          if_pos (sub_self n)]
        simpa only [mul_one] using (D.norm_diagonal_period_le (positiveIntegerIndex n hn) q hq).trans
          (by linarith : (80/Real.pi)*A ≤ (80/Real.pi)*A+1)
      · have hnk : positiveIntegerIndex n hn ≠ positiveIntegerIndex m hm :=
          (positiveIntegerIndex_eq_iff n m hn hm).not.mpr (Ne.symm hmn)
        have hb := D.norm_weighted_offDiagonal_period_le _ _ hnk q hq
        simp only [positiveIntegerIndex_real] at hb
        rw [if_neg (sub_ne_zero.mpr hmn),Int.cast_sub]
        apply hb.trans
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by
          have hc : (20/Real.pi)*A ≤ (80/Real.pi)*A :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right (by norm_num : (20 : ℝ) ≤ 80) Real.pi_pos.le) hA.le
          linarith) (by positivity)
    · rw [dif_neg hn,mul_zero,norm_zero]
      positivity
  · rw [dif_neg hm]
    by_cases hmn : m = n
    · subst n
      rw [if_pos rfl,div_self (NLS.Coeff.positiveIndexWeight_ne_zero m),mul_one,norm_one,
        sub_self,NLS.Coeff.norm_reciprocalSquareKernel_apply,if_pos rfl,mul_one]
      linarith
    · rw [if_neg hmn,mul_zero,norm_zero]
      positivity

theorem weightedMatrix_free (m n : ℤ) :
    classicalHillWeightedPeriodMatrix N 0 m n = if m = n then 1 else 0 := by
  rw [classicalHillWeightedPeriodMatrix,D.matrix_free]
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl,div_self (NLS.Coeff.positiveIndexWeight_ne_zero n),mul_one]
  · rw [if_neg hmn,mul_zero]

theorem weightedMatrix_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun q => classicalHillWeightedPeriodMatrix N q m n) V :=
  analyticOnNhd_const.mul (D.matrix_analytic m n)

/-- The selected data itself constructs the weighted operator, on the
identical neighborhood and with the exact rescaled integral entries. -/
theorem exists_weighted_period_operator :
    ∃ S : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      AnalyticOnNhd ℂ S V ∧
      (∀ q ∈ V, ‖S q‖ ≤ 5*((80/Real.pi)*A+1)) ∧
      (∀ q ∈ V, ∀ m n : ℤ, (S q (lp.single 2 n 1)) m = classicalHillWeightedPeriodMatrix N q m n) ∧
      S 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
  let M : ℝ := (80/Real.pi)*A+1
  have hA := D.amplitude_pos
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨S,hSa,hSnorm,hSentry⟩ := NLS.Coeff.exists_analytic_operator_of_convolution_dominated_matrix
    (classicalHillWeightedPeriodMatrix N) V D.isOpen D.weightedMatrix_analytic
    NLS.Coeff.reciprocalSquareKernel NLS.Coeff.reciprocalSquareKernel_ne_zero M hM.le D.weightedMatrix_bound
  refine ⟨S,hSa,?_,hSentry,?_⟩
  · intro q hq
    exact (hSnorm q hq).trans (by nlinarith [NLS.Coeff.norm_reciprocalSquareKernel_le])
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro n
  ext m
  rw [hSentry 0 D.zero_mem m n,D.weightedMatrix_free]
  simp only [ContinuousLinearMap.id_apply,lp.single_apply,Pi.single_apply]

end ClassicalAllContourPeriodData
end NLS.KdV
