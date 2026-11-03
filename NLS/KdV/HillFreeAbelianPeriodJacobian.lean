import NLS.KdV.HillFreeAbelianRootVariation
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillFreeAbelianPeriodJacobian (n m k : ℕ) : ℂ :=
  if m = n then 0 else
    ((if k = n then (1 : ℂ) else 0) -
      ((n : ℂ)/(m : ℂ))*(if k = m then 1 else 0)) /
        ((freeHillValue m : ℂ)-(freeHillValue n : ℂ))

theorem hillFreeAbelianPeriod_single_root_affine
    (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (t : ℝ) :
    hillAbelianCandidatePeriod 0 hq hr
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n k =
      (if k = n then (1 : ℂ) else 0) + (t : ℂ)*hillFreeAbelianPeriodJacobian n m k := by
  by_cases hmn : m = n
  · subst m
    have he (j : ℕ) (hj : j+1 ≠ n) :
        Function.update hillFreeGapRoot (n-1) (freeHillValue n+t) j = hillFreeGapRoot j := by
      exact Function.update_of_ne (by omega : j ≠ n-1) _ _
    rw [hillAbelianCandidatePeriod_congr_omitted 0 hq hr _ hillFreeGapRoot n k he,
      hillFreeAbelianPeriod_eq_delta hq hr n k hn hk,hillFreeAbelianPeriodJacobian,
      if_pos rfl,mul_zero,add_zero]
  · rw [hillFreeAbelianPeriod_single_root_variation hq hr n m k hn hm hk hmn t,
      hillFreeAbelianPeriod_eq_delta hq hr n k hn hk,
      hillFreeAbelianPeriod_eq_delta hq hr m k hm hk,
      hillFreeAbelianPeriodJacobian,if_neg hmn]
    ring

theorem hasDerivAt_hillFreeAbelianPeriod_single_root
    (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => hillAbelianCandidatePeriod 0 hq hr
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n k)
      (hillFreeAbelianPeriodJacobian n m k) t₀ := by
  have he : (fun t : ℝ => hillAbelianCandidatePeriod 0 hq hr
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n k) =
      (fun t : ℝ => (if k = n then (1 : ℂ) else 0) +
        (t : ℂ)*hillFreeAbelianPeriodJacobian n m k) := by
    funext t
    exact hillFreeAbelianPeriod_single_root_affine hq hr n m k hn hm hk t
  rw [he]
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t₀ :=
    (hasDerivAt_id t₀).ofReal_comp
  simpa only [one_mul] using
    (hc.mul_const (hillFreeAbelianPeriodJacobian n m k)).const_add
      (if k = n then (1 : ℂ) else 0)

theorem hillFreeAbelianPeriodJacobian_off_diagonal
    (n m k : ℕ) (hkn : k ≠ n) (hkm : k ≠ m) :
    hillFreeAbelianPeriodJacobian n m k = 0 := by
  by_cases hmn : m = n
  · simp only [hillFreeAbelianPeriodJacobian,if_pos hmn]
  · simp only [hillFreeAbelianPeriodJacobian,if_neg hmn,if_neg hkn,if_neg hkm,
      mul_zero,sub_self,zero_div]

theorem hillFreeAbelianPeriodJacobian_diagonal
    (n m : ℕ) (hmn : m ≠ n) :
    hillFreeAbelianPeriodJacobian n m m =
      -((n : ℂ)/(m : ℂ))/((freeHillValue m : ℂ)-(freeHillValue n : ℂ)) := by
  simp [hillFreeAbelianPeriodJacobian,hmn]

theorem hillFreeAbelianPeriodJacobian_diagonal_ne_zero
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    hillFreeAbelianPeriodJacobian n m m ≠ 0 := by
  rw [hillFreeAbelianPeriodJacobian_diagonal n m hmn]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact div_ne_zero (neg_ne_zero.mpr (div_ne_zero hn0 hm0))
    (sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hmn)))

theorem hillFreeAbelianPeriodJacobian_scaled
    (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) (hkn : k ≠ n) :
    (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)) *
      (m : ℂ)*hillFreeAbelianPeriodJacobian n m k = if k = m then -1 else 0 := by
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl,hillFreeAbelianPeriodJacobian_diagonal n m hmn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hmnE : (freeHillValue m : ℂ)-(freeHillValue n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hmn))
    field_simp
  · rw [if_neg hkm,hillFreeAbelianPeriodJacobian_off_diagonal n m k hkn hkm,mul_zero]

theorem hasDerivAt_hillFreeAbelianPeriod_scaled_single_root
    (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hmn : m ≠ n) (hkn : k ≠ n) :
    HasDerivAt (fun t : ℝ =>
      (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)) *
        hillAbelianCandidatePeriod 0 hq hr
          (Function.update hillFreeGapRoot (m-1) (freeHillValue m+(m : ℝ)*t)) n k)
      (if k = m then (-1 : ℂ) else 0) 0 := by
  have hi : HasDerivAt (fun t : ℝ => (m : ℝ)*t) (m : ℝ) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).const_mul (m : ℝ) using 1
    simp only [mul_one]
  have ho := hasDerivAt_hillFreeAbelianPeriod_single_root hq hr n m k hn hm hk ((m : ℝ)*0)
  have hc := (ho.scomp (0 : ℝ) hi).const_mul
    (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)) *
      ((m : ℝ) • hillFreeAbelianPeriodJacobian n m k) = if k = m then (-1 : ℂ) else 0 := by
    rw [Complex.real_smul,ofReal_natCast,← mul_assoc]
    exact hillFreeAbelianPeriodJacobian_scaled n m k hn hm hmn hkn
  simpa only [Function.comp_def,he] using hc

end NLS.KdV
