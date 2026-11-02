import NLS.KdV.ClassicalWeightedPeriodOperator
import NLS.SequenceSpaces.MixedMajorantMatrix
import NLS.SequenceSpaces.PositiveIndexPowerWeight

/-! # An actual Hill period operator with two index weights

The near-diagonal reciprocal-square bound and a far-off-diagonal Hilbert
outer-product bound are retained separately. Their combined majorant
constructs the twice-weighted operator on the same spectral neighborhood.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

def classicalHillTwoWeightedPeriodMatrix (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ)
    (m n : ℤ) : ℂ :=
  (NLS.Coeff.positiveIndexWeight m^2/NLS.Coeff.positiveIndexWeight n^2)*
    classicalHillPeriodMatrix N q m n

def classicalHillTwoWeightKernel : NLS.Coeff 1 :=
  (2 : ℂ) • NLS.Coeff.reciprocalSquareKernel

def classicalHillTwoWeightTail : NLS.Coeff 2 :=
  (2 : ℂ) • NLS.Coeff.puncturedLattice 2 (by norm_num)

theorem positiveIndex_twoWeighted_squared_energy_kernel_le (n k : ℕ+) (hnk : n ≠ k) :
    ((k : ℝ)/(n : ℝ))^2*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) ≤
      2/|(k : ℝ)-(n : ℝ)|^2+4/((n : ℝ)*(k : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hkn : (k : ℝ)-(n : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have he' : ((k : ℕ) : ℝ) = ((n : ℕ) : ℝ) := he
    exact hnk (Subtype.ext (Nat.cast_injective he'.symm))
  have hd : (k : ℝ)^2-(n : ℝ)^2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by positivity) hkn
  by_cases hnear : (k : ℝ) ≤ 2*(n : ℝ)
  · have hratio : (k : ℝ)/(n : ℝ) ≤ 2 := (div_le_iff₀ hn).mpr hnear
    calc
      _ = ((k : ℝ)/(n : ℝ))*(((k : ℝ)/(n : ℝ))*
          ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) := by ring
      _ ≤ ((k : ℝ)/(n : ℝ))*(1/|(k : ℝ)-(n : ℝ)|^2) :=
        mul_le_mul_of_nonneg_left (positiveIndex_weighted_squared_energy_kernel_le n k hnk) (by positivity)
      _ ≤ 2*(1/|(k : ℝ)-(n : ℝ)|^2) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ _ := by
        rw [← mul_div_assoc,mul_one]
        exact le_add_of_nonneg_right (by positivity)
  · have hs := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2*(n : ℝ))
        (by linarith : 2*(n : ℝ) ≤ (k : ℝ))
    have hdiff : (k : ℝ)^2/2 ≤ (k : ℝ)^2-(n : ℝ)^2 := by nlinarith
    have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ)^2/2) hdiff 2
    have hfour : (k : ℝ)^4 ≤ 4*|(k : ℝ)^2-(n : ℝ)^2|^2 := by
      rw [sq_abs]
      nlinarith
    have he : ((k : ℝ)/(n : ℝ))^2*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) =
        (k : ℝ)^3/((n : ℝ)*|(k : ℝ)^2-(n : ℝ)^2|^2) := by field_simp
    have hfar : (k : ℝ)^3/((n : ℝ)*|(k : ℝ)^2-(n : ℝ)^2|^2) ≤ 4/((n : ℝ)*(k : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hn (sq_pos_of_ne_zero (abs_ne_zero.mpr hd))) (mul_pos hn hk)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hfour hn.le]
    rw [he]
    exact hfar.trans (le_add_of_nonneg_left (by positivity))

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem norm_twoWeighted_offDiagonal_period_le (n k : ℕ+) (hnk : n ≠ k)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    ((k : ℝ)/(n : ℝ))^2*‖classicalHillUniformHighPeriod N n k q‖ ≤
      ((20/Real.pi)*A)*(2/|(k : ℝ)-(n : ℝ)|^2+4/((n : ℝ)*(k : ℝ))) := by
  have hb := norm_classicalHillUniformHighPeriod_le N n k hnk q (I*(k : ℂ)*Real.pi) A
    D.amplitude_pos.le (D.numerator_factor n q hq) (D.cover k q hq)
    (D.offDiagonal_separation n k hnk q hq) (D.primitive_bound k q hq)
  have hraw : ‖classicalHillUniformHighPeriod N n k q‖ ≤
      ((20/Real.pi)*A)*((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2) := by
    convert hb using 1
    ring
  have hA := D.amplitude_pos
  calc
    _ ≤ ((k : ℝ)/(n : ℝ))^2*(((20/Real.pi)*A)*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) :=
      mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
    _ = ((20/Real.pi)*A)*(((k : ℝ)/(n : ℝ))^2*
        ((n : ℝ)*(k : ℝ)/|(k : ℝ)^2-(n : ℝ)^2|^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (positiveIndex_twoWeighted_squared_energy_kernel_le n k hnk) (by positivity)

end ClassicalAllContourPeriodData

theorem classicalHillTwoWeightKernel_ne_zero (d : ℤ) : classicalHillTwoWeightKernel d ≠ 0 := by
  change (2 : ℂ)*NLS.Coeff.reciprocalSquareKernel d ≠ 0
  exact mul_ne_zero (by norm_num) (NLS.Coeff.reciprocalSquareKernel_ne_zero d)

theorem classicalHillTwoWeightMajorant_offDiagonal (m n : ℤ)
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    NLS.Coeff.mixedMatrixMajorant classicalHillTwoWeightKernel
      classicalHillTwoWeightTail classicalHillTwoWeightTail m n =
        2/|(m : ℝ)-(n : ℝ)|^2+4/((n : ℝ)*(m : ℝ)) := by
  dsimp only [NLS.Coeff.mixedMatrixMajorant,classicalHillTwoWeightKernel,classicalHillTwoWeightTail]
  simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_ofNat,
    NLS.Coeff.norm_reciprocalSquareKernel_apply,if_neg (sub_ne_zero.mpr hmn),
    NLS.Coeff.puncturedLattice_apply,if_neg (ne_of_gt hm),if_neg (ne_of_gt hn),
    norm_inv,Complex.norm_intCast,abs_of_pos (by exact_mod_cast hm : (0 : ℝ) < m),
    abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n),Int.cast_sub]
  field_simp
  ring

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem twoWeightedMatrix_bound (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (m n : ℤ) :
    ‖classicalHillTwoWeightedPeriodMatrix N q m n‖ ≤
      ((80/Real.pi)*A+1)*NLS.Coeff.mixedMatrixMajorant classicalHillTwoWeightKernel
        classicalHillTwoWeightTail classicalHillTwoWeightTail m n := by
  have hA := D.amplitude_pos
  have hM : 0 < (80/Real.pi)*A+1 := by positivity
  by_cases hmn : m = n
  · subst n
    rw [classicalHillTwoWeightedPeriodMatrix,div_self (pow_ne_zero 2 (NLS.Coeff.positiveIndexWeight_ne_zero m)),one_mul]
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
  unfold classicalHillTwoWeightedPeriodMatrix classicalHillPeriodMatrix
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
    classicalHillTwoWeightedPeriodMatrix N 0 m n = if m = n then 1 else 0 := by
  rw [classicalHillTwoWeightedPeriodMatrix,D.matrix_free]
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl,div_self (pow_ne_zero 2 (NLS.Coeff.positiveIndexWeight_ne_zero n)),mul_one]
  · rw [if_neg hmn,mul_zero]

theorem twoWeightedMatrix_analytic (m n : ℤ) :
    AnalyticOnNhd ℂ (fun q => classicalHillTwoWeightedPeriodMatrix N q m n) V :=
  analyticOnNhd_const.mul (D.matrix_analytic m n)

/-- All actual twice-weighted entries are assembled into one analytic
bounded operator, with the extra far tail proved rather than discarded. -/
theorem exists_twoWeighted_period_operator :
    ∃ S : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      AnalyticOnNhd ℂ S V ∧
      (∀ q ∈ V, ‖S q‖ ≤ 26*((80/Real.pi)*A+1)) ∧
      (∀ q ∈ V, ∀ m n : ℤ, (S q (lp.single 2 n 1)) m = classicalHillTwoWeightedPeriodMatrix N q m n) ∧
      S 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
  let M : ℝ := (80/Real.pi)*A+1
  have hA := D.amplitude_pos
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨S,hSa,hSnorm,hSentry⟩ := NLS.Coeff.exists_analytic_operator_of_mixed_majorant_matrix
    (classicalHillTwoWeightedPeriodMatrix N) V D.isOpen D.twoWeightedMatrix_analytic
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

end ClassicalAllContourPeriodData
end NLS.KdV
