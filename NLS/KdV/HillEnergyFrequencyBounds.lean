import NLS.KdV.HillCanonicalEnergyRootProduct
import NLS.ComplexAnalysis.ComplexSquareRootShift

/-! # Actual energy endpoint square roots have inverse-index frequency bounds and square-summable positive-frequency displacements. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem hillRealLabels_sqrt_frequency_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ‖Complex.sqrt (hillRealLabels q hq hr (2*n-1))-(Real.pi : ℂ)*n‖ ≤ 4*‖q‖/(Real.pi*n) ∧
    ‖Complex.sqrt (hillRealLabels q hq hr (2*n))-(Real.pi : ℂ)*n‖ ≤ 4*‖q‖/(Real.pi*n) := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hloc := p.localization q hq n (by omega) (by linarith [norm_nonneg q])
  have hc : 0 < Real.pi*(n : ℝ) := mul_pos Real.pi_pos (by exact_mod_cast (show 0 < n by omega))
  have hlo : ‖(hillRealLabels q hq hr (2*n-1) : ℂ)-((Real.pi*(n : ℝ) : ℝ) : ℂ)^2‖ ≤ 4*‖q‖ := by
    rw [← ofReal_pow,← ofReal_sub,norm_real,Real.norm_eq_abs,hl]
    simpa only [freeHillValue,Int.cast_natCast,mul_pow] using hloc.1
  have hup : ‖(hillRealLabels q hq hr (2*n) : ℂ)-((Real.pi*(n : ℝ) : ℝ) : ℂ)^2‖ ≤ 4*‖q‖ := by
    rw [← ofReal_pow,← ofReal_sub,norm_real,Real.norm_eq_abs,hu]
    simpa only [freeHillValue,Int.cast_natCast,mul_pow] using hloc.2
  constructor
  · simpa only [ofReal_mul,ofReal_natCast] using norm_complexSqrt_sub_positive_le
      (hillRealLabels q hq hr (2*n-1)) (Real.pi*n) (4*‖q‖) hc hlo
  · simpa only [ofReal_mul,ofReal_natCast] using norm_complexSqrt_sub_positive_le
      (hillRealLabels q hq hr (2*n)) (Real.pi*n) (4*‖q‖) hc hup

def hillEnergyFrequencyRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (n : ℕ) : ℂ :=
  Complex.sqrt (hillRealLabels q hq hr (if upper then 2*n else 2*n-1))

theorem memℓp_hillEnergyFrequencyRoot_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) :
    Memℓp (fun k : ℕ => hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(k+1 : ℕ)) 2 := by
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
  have hbound : ‖hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(k+1 : ℕ)‖ ≤
      4*‖q‖/(Real.pi*(k+1 : ℕ)) := by
    have h := hillRealLabels_sqrt_frequency_bound q hq hr (k+1) hn2 hcut
    cases upper with
    | false => exact h.1
    | true => exact h.2
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  simpa only [div_pow,mul_pow,div_div] using hsq

end NLS.KdV
