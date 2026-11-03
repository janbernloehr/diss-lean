import NLS.KdV.HillHminusOnePeriodInverse
import NLS.KdV.ClassicalTwoWeightedPeriodOperator

/-! # The actual rough Hill period operator with two index weights

Actual squared-energy separation retains both a summable near-diagonal
kernel and a far Hilbert outer product. No weighted inverse is assumed.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusTwoWeightedPeriodMatrix (C : HillHminusMiuraChart) (N : ℕ)
    (q : PeriodOneHminusOne) (m n : ℤ) : ℂ :=
  (NLS.Coeff.positiveIndexWeight m^2/NLS.Coeff.positiveIndexWeight n^2)*
    hillHminusPeriodMatrix C N q m n

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem norm_offDiagonal_energy_period_le (n k : ℕ+) (hnk : n ≠ k) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ‖hillHminusPeriodEntry C N n k q‖ ≤ ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
  have hA := D.amplitude_pos
  let d : ℝ := Real.pi^2/4*|(k : ℝ)^2-(n : ℝ)^2|
  have hd : 0 < d := by
    dsimp only [d]
    exact mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k n (Ne.symm hnk)))
  have hsep := D.offDiagonal_separation n k hnk q hq
  have hne (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      z^2-hillHminusUniformCriticalPoint C N n q ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep z hz))
  rw [D.period_eq_primitive n k q hq (I*(k : ℂ)*Real.pi) hne,norm_mul,Complex.norm_natCast]
  have hi := norm_frequency_primitive_resolvent_integral_le
    (fun z => hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)
    (hillHminusUniformCriticalPoint C N n q) k A d hA.le hd (D.primitive_bound k q hq) hsep
  calc
    _ ≤ (n : ℝ)*(2*Real.pi*(Real.pi/4)*(A*((5*Real.pi/2)*(k : ℝ))/d^2)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
      dsimp only [d]
      field_simp
      ring

theorem norm_twoWeighted_offDiagonal_period_le (n k : ℕ+) (hnk : n ≠ k)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    ((k : ℝ)/(n : ℝ))^2*‖hillHminusPeriodEntry C N n k q‖ ≤
      ((20/Real.pi)*A)*(2/|(k : ℝ)-(n : ℝ)|^2+4/((n : ℝ)*(k : ℝ))) := by
  have hraw := D.norm_offDiagonal_energy_period_le n k hnk q hq
  have hA := D.amplitude_pos
  calc
    _ ≤ ((k : ℝ)/(n : ℝ))^2*(((20/Real.pi)*A)*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) :=
      mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ = ((20/Real.pi)*A)*(((k : ℝ)/(n : ℝ))^2*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (positiveIndex_twoWeighted_squared_energy_kernel_le n k hnk) (by positivity)

theorem twoWeightedMatrix_bound (q : PeriodOneHminusOne) (hq : q ∈ V) (m n : ℤ) :
    ‖hillHminusTwoWeightedPeriodMatrix C N q m n‖ ≤
      ((80/Real.pi)*A+1)*NLS.Coeff.mixedMatrixMajorant classicalHillTwoWeightKernel
        classicalHillTwoWeightTail classicalHillTwoWeightTail m n := by
  have hA := D.amplitude_pos
  have hM : 0 < (80/Real.pi)*A+1 := by positivity
  by_cases hmn : m = n
  · subst n
    rw [hillHminusTwoWeightedPeriodMatrix,div_self (pow_ne_zero 2 (NLS.Coeff.positiveIndexWeight_ne_zero m)),one_mul]
    have hb := D.matrix_bound q hq m m
    simp only [sub_self,NLS.Coeff.norm_reciprocalSquareKernel_apply,ite_true,mul_one] at hb
    apply hb.trans
    have hc : 1 ≤ NLS.Coeff.mixedMatrixMajorant classicalHillTwoWeightKernel
        classicalHillTwoWeightTail classicalHillTwoWeightTail m m := by
      dsimp only [NLS.Coeff.mixedMatrixMajorant,classicalHillTwoWeightKernel]
      simp only [sub_self,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_ofNat,
        NLS.Coeff.norm_reciprocalSquareKernel_apply,ite_true,mul_one]
      nlinarith [sq_nonneg ‖classicalHillTwoWeightTail m‖]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc hM.le
  unfold hillHminusTwoWeightedPeriodMatrix hillHminusPeriodMatrix
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    by_cases hn : 0 < n
    · rw [dif_pos hn]
      simp only [NLS.Coeff.positiveIndexWeight,if_pos hm,if_pos hn,norm_mul,norm_div,norm_pow,
        Complex.norm_intCast,abs_of_pos (by exact_mod_cast hm : (0 : ℝ) < m),
        abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n),← div_pow]
      have hnk : positiveIntegerIndex n hn ≠ positiveIntegerIndex m hm :=
        (positiveIntegerIndex_eq_iff n m hn hm).not.mpr (Ne.symm hmn)
      have hb := D.norm_twoWeighted_offDiagonal_period_le _ _ hnk q hq
      simp only [positiveIntegerIndex_real] at hb
      rw [← classicalHillTwoWeightMajorant_offDiagonal m n hm hn hmn] at hb
      apply hb.trans
      have hc : (20/Real.pi)*A ≤ (80/Real.pi)*A+1 := by
        have hh := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by norm_num : (20 : ℝ) ≤ 80) Real.pi_pos.le) hA.le
        linarith
      exact mul_le_mul_of_nonneg_right hc (by
        unfold NLS.Coeff.mixedMatrixMajorant
        positivity)
    · rw [dif_neg hn,mul_zero,norm_zero]
      unfold NLS.Coeff.mixedMatrixMajorant
      positivity
  · rw [dif_neg hm,if_neg hmn,mul_zero,norm_zero]
    unfold NLS.Coeff.mixedMatrixMajorant
    positivity

theorem twoWeightedMatrix_free (m n : ℤ) :
    hillHminusTwoWeightedPeriodMatrix C N 0 m n = if m = n then 1 else 0 := by
  rw [hillHminusTwoWeightedPeriodMatrix,D.matrix_free]
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl,div_self (pow_ne_zero 2 (NLS.Coeff.positiveIndexWeight_ne_zero n)),mul_one]
  · rw [if_neg hmn,mul_zero]

theorem twoWeightedMatrix_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun q => hillHminusTwoWeightedPeriodMatrix C N q m n) V :=
  analyticOnNhd_const.mul (D.matrix_analytic m n)

/-- All actual twice-weighted entries are assembled into one analytic
bounded operator, with the extra far tail proved rather than discarded. -/
theorem exists_twoWeighted_period_operator :
    ∃ S : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      AnalyticOnNhd ℂ S V ∧
      (∀ q ∈ V, ‖S q‖ ≤ 26*((80/Real.pi)*A+1)) ∧
      (∀ q ∈ V, ∀ m n : ℤ, (S q (lp.single 2 n 1)) m = hillHminusTwoWeightedPeriodMatrix C N q m n) ∧
      S 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
  let M : ℝ := (80/Real.pi)*A+1
  have hA := D.amplitude_pos
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨S,hSa,hSnorm,hSentry⟩ := NLS.Coeff.exists_analytic_operator_of_mixed_majorant_matrix
    (hillHminusTwoWeightedPeriodMatrix C N) V D.isOpen D.twoWeightedMatrix_analytic
    classicalHillTwoWeightKernel classicalHillTwoWeightKernel_ne_zero
    classicalHillTwoWeightTail classicalHillTwoWeightTail M hM.le D.twoWeightedMatrix_bound
  have hb : ‖classicalHillTwoWeightKernel‖ ≤ 10 := by
    rw [classicalHillTwoWeightKernel,norm_smul,Complex.norm_ofNat]
    linarith [NLS.Coeff.norm_reciprocalSquareKernel_le]
  have hu : ‖classicalHillTwoWeightTail‖ ≤ 4 := by
    rw [classicalHillTwoWeightTail,norm_smul,Complex.norm_ofNat]
    linarith [NLS.Coeff.norm_puncturedLattice_two_le]
  have hC : ‖classicalHillTwoWeightKernel‖+‖classicalHillTwoWeightTail‖*‖classicalHillTwoWeightTail‖ ≤ 26 := by
    nlinarith [norm_nonneg classicalHillTwoWeightTail]
  refine ⟨S,hSa,?_,hSentry,?_⟩
  · intro q hq
    exact (hSnorm q hq).trans (by nlinarith [mul_le_mul_of_nonneg_left hC hM.le])
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro n
  ext m
  rw [hSentry 0 D.zero_mem m n,D.twoWeightedMatrix_free]
  simp only [ContinuousLinearMap.id_apply,lp.single_apply,Pi.single_apply]

end HillHminusUniformPeriodData
end NLS.KdV
