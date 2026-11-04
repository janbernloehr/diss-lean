import NLS.KdV.HillAnalyticPeriodBranch

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianComplexPeriod_high_eq_zero_of_mixed
    (N n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkN : N ≤ k) (hkn : k ≠ n)
    (a p : Coeff 2) (hzero : hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p) = 0) :
    hillAbelianComplexPeriod 0 h0q h0r n k (a,p) = 0 := by
  have h := congrArg (fun v : Coeff 2 => v (k : ℤ)) hzero
  rw [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n k hn hk,
    if_pos hkn,if_neg (by omega : ¬k < N)] at h
  change (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianComplexPeriod 0 h0q h0r n k (a,p) = 0 at h
  have hne : ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ) ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (strictMono_freeHillValue.injective.ne hkn)))
      (by exact_mod_cast (show n ≠ 0 by omega))
  exact (mul_eq_zero.mp h).resolve_left hne

theorem circleIntegral_hillComplexBranch_high_eq_zero_of_mixed
    (N n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkN : N ≤ k) (hkn : k ≠ n)
    (a p : Coeff 2) (P : ℂ)
    (hzero : hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p) = 0) :
    (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      (hillAbelianHilbertPsi n (E,a)/P)/hillAbelianComplexRoot 0 h0q h0r (E,p)) = 0 := by
  have hp := hillAbelianComplexPeriod_high_eq_zero_of_mixed q hq hr h0q h0r N n k hn hk hkN hkn a p hzero
  unfold hillAbelianComplexPeriod at hp
  have hcoef : (2*(Real.pi : ℂ))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hraw := (mul_eq_zero.mp hp).resolve_left hcoef
  have he (E : ℂ) : (hillAbelianHilbertPsi n (E,a)/P)/hillAbelianComplexRoot 0 h0q h0r (E,p) =
      (hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p))/P := by ring
  simp_rw [he]
  have he' (E : ℂ) : (hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p))/P =
      P⁻¹*(hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p)) := by ring
  simp_rw [he']
  rw [circleIntegral.integral_const_mul,hraw,mul_zero]

end NLS.KdV
