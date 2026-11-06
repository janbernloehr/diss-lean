import NLS.KdV.HillAbelianHilbertInput
import NLS.KdV.HillAbelianProductZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



def hillAbelianComplexNumeratorFactor (n : ℕ) (t : ℂ × Coeff 2) (k : ℕ) : ℂ :=
  if k+1 = n then 1 else
    ((freeHillValue (k+1 : ℕ) : ℂ) + ((k+1 : ℕ) : ℂ)*t.2 ((k+1 : ℕ) : ℤ)-t.1) /
      (freeHillValue (k+1 : ℕ) : ℂ)

theorem hillAbelianComplexNumeratorFactor_eq_hilbert (n : ℕ) (t : ℂ × Coeff 2) (k : ℕ) :
    hillAbelianComplexNumeratorFactor n t k =
      1+hillAbelianHilbertInput t ((k+1 : ℕ) : ℤ)*
        hillAbelianHilbertWeight n ((k+1 : ℕ) : ℤ) := by
  rw [hillAbelianHilbertWeight_positive]
  unfold hillAbelianComplexNumeratorFactor
  by_cases hkn : k+1 = n
  · simp only [if_pos hkn,mul_zero,add_zero]
  · rw [if_neg hkn,if_neg hkn,hillAbelianHilbertInput_apply,
      Coeff.positivePuncturedLattice_natSucc]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k+1 ≠ 0)
    have hE : (freeHillValue (k+1 : ℕ) : ℂ) = (Real.pi : ℂ)^2*((k+1 : ℕ) : ℂ)^2 := by
      simp only [freeHillValue,ofReal_mul,ofReal_pow]
      push_cast
      rfl
    rw [hE]
    field_simp
    ring

theorem summable_norm_hillAbelianComplexNumeratorFactor_sub_one (n : ℕ) (t : ℂ × Coeff 2) :
    Summable (fun k : ℕ => ‖hillAbelianComplexNumeratorFactor n t k-1‖) := by
  have hi : Function.Injective (fun k : ℕ => ((k+1 : ℕ) : ℤ)) := by
    intro k j h
    change ((k+1 : ℕ) : ℤ) = ((j+1 : ℕ) : ℤ) at h
    have hj : k+1 = j+1 := by exact_mod_cast h
    omega
  have h := (summable_norm_hilbertProductInput (hillAbelianHilbertWeight n)
    (hillAbelianHilbertInput t)).comp_injective hi
  simp only [hillAbelianComplexNumeratorFactor_eq_hilbert,add_sub_cancel_left]
  convert! h using 1

theorem multipliable_hillAbelianComplexNumeratorFactors (n : ℕ) (t : ℂ × Coeff 2) :
    Multipliable (hillAbelianComplexNumeratorFactor n t) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_hillAbelianComplexNumeratorFactor_sub_one n t)
  convert! h using 1
  funext k
  ring

theorem hillAbelianHilbertPartialProduct_eq (n : ℕ) (t : ℂ × Coeff 2) (N : ℕ) :
    hilbertWeightedPartialProduct (hillAbelianHilbertWeight n) N (hillAbelianHilbertInput t) =
      ∏ k ∈ Finset.range N, hillAbelianComplexNumeratorFactor n t k := by
  rw [hilbertWeightedPartialProduct,prod_symmetric_interval]
  have hz := hillAbelianHilbertWeight_nonpositive n 0 le_rfl
  rw [hz,mul_zero,add_zero,one_mul]
  apply Finset.prod_congr rfl
  intro k _
  rw [hillAbelianHilbertWeight_nonpositive n (-((k : ℤ)+1)) (by omega),
    mul_zero,add_zero,mul_one]
  have he : (k : ℤ)+1 = ((k+1 : ℕ) : ℤ) := by omega
  rw [he]
  exact (hillAbelianComplexNumeratorFactor_eq_hilbert n t k).symm

theorem hillAbelianHilbertProduct_eq_tprod (n : ℕ) (t : ℂ × Coeff 2) :
    hillAbelianHilbertProduct n t = ∏' k : ℕ, hillAbelianComplexNumeratorFactor n t k := by
  have h := tendsto_hilbertWeightedPartialProduct (hillAbelianHilbertWeight n)
    (hillAbelianHilbertInput t)
  simp only [hillAbelianHilbertPartialProduct_eq] at h
  exact tendsto_nhds_unique h (multipliable_hillAbelianComplexNumeratorFactors n t).hasProd.tendsto_prod_nat

def hillAbelianHilbertPsi (n : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  2/((n : ℂ)*Real.pi)*hillAbelianHilbertProduct n t

theorem analyticOnNhd_hillAbelianHilbertPsi (n : ℕ) :
    AnalyticOnNhd ℂ (hillAbelianHilbertPsi n) univ :=
  analyticOnNhd_const.mul (analyticOnNhd_hillAbelianHilbertProduct n)

theorem hillAbelianHilbertProduct_eq_real_numerator (n : ℕ) (energy : ℂ)
    (a : Coeff 2) (σ : ℕ → ℝ)
    (ha : ∀ k : ℕ, (σ k : ℂ) = (freeHillValue (k+1 : ℕ) : ℂ) +
      ((k+1 : ℕ) : ℂ)*a ((k+1 : ℕ) : ℤ)) :
    hillAbelianHilbertProduct n (energy,a) = hillAbelianNumeratorProduct σ n energy := by
  rw [hillAbelianHilbertProduct_eq_tprod,hillAbelianNumeratorProduct]
  congr 1
  funext k
  unfold hillAbelianComplexNumeratorFactor hillAbelianNumeratorFactor hillGapRootEnergyFactor
  split_ifs
  · rfl
  · rw [ha]

theorem hillAbelianHilbertPsi_eq_real_candidate (n : ℕ) (energy : ℂ)
    (a : Coeff 2) (σ : ℕ → ℝ)
    (ha : ∀ k : ℕ, (σ k : ℂ) = (freeHillValue (k+1 : ℕ) : ℂ) +
      ((k+1 : ℕ) : ℂ)*a ((k+1 : ℕ) : ℤ)) :
    hillAbelianHilbertPsi n (energy,a) = hillAbelianPsiCandidate σ n energy := by
  rw [hillAbelianHilbertPsi,hillAbelianPsiCandidate,
    hillAbelianHilbertProduct_eq_real_numerator n energy a σ ha]

end NLS.KdV
