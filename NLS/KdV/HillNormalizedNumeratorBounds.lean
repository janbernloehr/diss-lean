import NLS.KdV.HillCommonMixedNormalizedPsi
import NLS.KdV.HillProductPeriodBoundedRoots

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- On bounded energy and root sets, the actual normalized numerator
has its original inverse-index size, with the genuine own-period bound. -/
theorem norm_hillMixedNormalizedComplexPsi_le_of_bounds
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2) (E : ℂ) (A T c : ℝ)
    (hc : 0<c) (ha : ‖a‖≤A) (hE : ‖E‖≤T)
    (hown : c≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a,p)‖) :
    ‖hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a,p) E‖≤
      (2/((n : ℝ)*Real.pi))*Real.exp ((A+2*T)*‖hillAbelianHilbertWeight 0‖)/c := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  unfold hillMixedNormalizedComplexPsi hillAbelianHilbertPsi
  rw [norm_div,norm_mul,norm_div,norm_mul,norm_ofNat,norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply div_le_div₀ (by positivity) ?_ hc hown
  exact mul_le_mul_of_nonneg_left (norm_hillAbelianHilbertProduct_le_of_bounds n E a A T ha hE)
    (by positivity : 0≤2/((n : ℝ)*Real.pi))

/-- The bound is uniform in every positive differential index. -/
theorem norm_hillMixedNormalizedComplexPsi_uniform_le_of_bounds
    (N n : ℕ) (hn : 1≤n) (a p : Coeff 2) (E : ℂ) (A T c : ℝ)
    (hc : 0<c) (ha : ‖a‖≤A) (hE : ‖E‖≤T)
    (hown : c≤‖hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a,p)‖) :
    ‖hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a,p) E‖≤
      (2/Real.pi)*Real.exp ((A+2*T)*‖hillAbelianHilbertWeight 0‖)/c := by
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn
  apply (norm_hillMixedNormalizedComplexPsi_le_of_bounds q hq hr h0q h0r N n hn a p E A T c hc ha hE hown).trans
  apply div_le_div_of_nonneg_right _ hc.le
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤2) Real.pi_pos
  nlinarith [Real.pi_pos]

end NLS.KdV
