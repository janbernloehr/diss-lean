import NLS.KdV.HillComplexNormalizedPeriodGerm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



theorem hillAbelianHilbertProduct_ne_zero_iff (n : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertProduct n (E,a) ≠ 0 ↔ ∀ j : ℕ, j+1 ≠ n →
      (freeHillValue (j+1 : ℕ) : ℂ)+((j+1 : ℕ) : ℂ)*a ((j+1 : ℕ) : ℤ) ≠ E := by
  have hs := summable_norm_hillAbelianComplexNumeratorFactor_sub_one n (E,a)
  have he (j : ℕ) : 1+(hillAbelianComplexNumeratorFactor n (E,a) j-1) =
      hillAbelianComplexNumeratorFactor n (E,a) j := by ring
  have hp := tprod_one_add_ne_zero_iff (fun j => hillAbelianComplexNumeratorFactor n (E,a) j-1) hs
  simp only [he] at hp
  rw [hillAbelianHilbertProduct_eq_tprod,hp]
  constructor
  · intro h j hj hz
    have hh := h j
    simp only [hillAbelianComplexNumeratorFactor,if_neg hj,hz,sub_self,zero_div,ne_eq,not_true_eq_false] at hh
  · intro h j
    unfold hillAbelianComplexNumeratorFactor
    split_ifs with hj
    · norm_num
    · exact div_ne_zero (sub_ne_zero.mpr (h j hj)) (hillGapRootEnergyFactor_denominator_ne_zero j)

theorem hillAbelianHilbertProduct_zero_iff (n : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertProduct n (E,a) = 0 ↔ ∃ j : ℕ, j+1 ≠ n ∧
      (freeHillValue (j+1 : ℕ) : ℂ)+((j+1 : ℕ) : ℂ)*a ((j+1 : ℕ) : ℤ) = E := by
  have h := not_congr (hillAbelianHilbertProduct_ne_zero_iff n E a)
  simpa only [not_not,not_forall,exists_prop] using h

theorem hillAbelianHilbertPsi_zero_iff (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertPsi n (E,a) = 0 ↔ ∃ j : ℕ, j+1 ≠ n ∧
      (freeHillValue (j+1 : ℕ) : ℂ)+((j+1 : ℕ) : ℂ)*a ((j+1 : ℕ) : ℤ) = E := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : (2 : ℂ)/((n : ℂ)*Real.pi) ≠ 0 := div_ne_zero (by norm_num)
    (mul_ne_zero hn0 (ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [hillAbelianHilbertPsi,mul_eq_zero]
  simp only [hp,false_or]
  exact hillAbelianHilbertProduct_zero_iff n E a

theorem hillAbelianNormalizedComplexPsi_zero_iff
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ) (t : Coeff 2 × Coeff 2)
    (ht : hillAbelianComplexPeriod 0 hq hr n n t ≠ 0) :
    hillAbelianNormalizedComplexPsi hq hr n t E = 0 ↔ ∃ j : ℕ, j+1 ≠ n ∧
      (freeHillValue (j+1 : ℕ) : ℂ)+((j+1 : ℕ) : ℂ)*t.1 ((j+1 : ℕ) : ℤ) = E := by
  rw [hillAbelianNormalizedComplexPsi,div_eq_zero_iff]
  simp only [ht,or_false]
  exact hillAbelianHilbertPsi_zero_iff n hn E t.1

end NLS.KdV
