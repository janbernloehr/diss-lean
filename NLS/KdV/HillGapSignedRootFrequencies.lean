import NLS.KdV.HillAbelianNumeratorProduct
import NLS.ComplexAnalysis.ComplexSquareRootShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillGapSignedRootFrequency
    (roots : ℕ → ℝ) (n : ℤ) : ℂ :=
  if n = 0 then 0 else if n < 0 then -Complex.sqrt (roots (n.natAbs-1))
    else Complex.sqrt (roots (n.natAbs-1))

@[simp] theorem hillGapSignedRootFrequency_natSucc
    (roots : ℕ → ℝ) (k : ℕ) :
    hillGapSignedRootFrequency roots ((k+1 : ℕ) : ℤ) = Complex.sqrt (roots k) := by
  unfold hillGapSignedRootFrequency
  rw [if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : ¬((k+1 : ℕ) : ℤ) < 0),Int.natAbs_natCast]
  simp only [Nat.add_sub_cancel]

@[simp] theorem hillGapSignedRootFrequency_negNatSucc
    (roots : ℕ → ℝ) (k : ℕ) :
    hillGapSignedRootFrequency roots (-((k+1 : ℕ) : ℤ)) = -Complex.sqrt (roots k) := by
  unfold hillGapSignedRootFrequency
  rw [if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),if_pos (by omega : -((k+1 : ℕ) : ℤ) < 0),
    Int.natAbs_neg,Int.natAbs_natCast]
  simp only [Nat.add_sub_cancel]

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillGapRoot_sqrt_frequency_bound
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ‖Complex.sqrt (roots (n-1))-(Real.pi : ℂ)*n‖ ≤ 4*‖q‖/(Real.pi*n) := by
  have hloc := hillGapRoot_high_localization q hq hr roots hroots n hn hcut
  have hc : 0 < Real.pi*(n : ℝ) := mul_pos Real.pi_pos (by exact_mod_cast (show 0 < n by omega))
  have he : (((Real.pi*(n : ℝ) : ℝ) : ℂ))^2 = (freeHillValue n : ℂ) := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
    push_cast
    ring
  have hh : ‖(roots (n-1) : ℂ)-((Real.pi*(n : ℝ) : ℝ) : ℂ)^2‖ ≤ 4*‖q‖ := by
    rw [he,← ofReal_sub,norm_real,Real.norm_eq_abs]
    exact hloc
  simpa only [ofReal_mul,ofReal_natCast] using norm_complexSqrt_sub_positive_le
    (roots (n-1)) (Real.pi*n) (4*‖q‖) hc hh

theorem memℓp_hillGapRoot_sqrt_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) :
    Memℓp (fun k : ℕ => Complex.sqrt (roots k)-(Real.pi : ℂ)*(k+1 : ℕ)) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun k : ℕ => (4*‖q‖/Real.pi)^2/((k+1 : ℕ) : ℝ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using ((summable_nat_add_iff 1).mpr hs0).mul_left ((4*‖q‖/Real.pi)^2)
  apply hs.of_norm_bounded_eventually_nat
  obtain ⟨N,hN⟩ := exists_nat_gt (16*‖q‖+2)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkR : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : 2 ≤ k+1 := by
    have hn : (2 : ℝ) < k := by linarith [norm_nonneg q]
    exact_mod_cast (show (2 : ℝ) ≤ (k+1 : ℕ) by push_cast; linarith)
  have hcut : 16*‖q‖ ≤ (k+1 : ℕ) := by push_cast; linarith
  have hbound : ‖Complex.sqrt (roots k)-(Real.pi : ℂ)*(k+1 : ℕ)‖ ≤
      4*‖q‖/(Real.pi*(k+1 : ℕ)) := by
    exact hillGapRoot_sqrt_frequency_bound q hq hr roots hroots (k+1) hn2 hcut
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  simpa only [div_pow,mul_pow,div_div] using hsq


theorem memℓp_hillGapSignedRootFrequency_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) :
    Memℓp (fun n : ℤ => hillGapSignedRootFrequency roots n-(Real.pi : ℂ)*n) 2 := by
  have hs := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp
    (memℓp_hillGapRoot_sqrt_displacement q hq hr roots hroots)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply Summable.of_nat_of_neg
  · apply (summable_nat_add_iff 1).mp
    simpa only [hillGapSignedRootFrequency_natSucc,Int.cast_natCast] using hs
  · apply (summable_nat_add_iff 1).mp
    convert! hs using 1
    funext k
    rw [hillGapSignedRootFrequency_negNatSucc]
    simp only [Int.cast_neg,Int.cast_natCast]
    rw [show -Complex.sqrt (roots k)-(Real.pi : ℂ)*(-((k+1 : ℕ) : ℂ)) =
      -(Complex.sqrt (roots k)-(Real.pi : ℂ)*(k+1 : ℕ)) by ring,norm_neg]

end NLS.KdV
