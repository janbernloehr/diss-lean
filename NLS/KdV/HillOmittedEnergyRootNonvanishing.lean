import NLS.KdV.HillOmittedEnergyRootProduct
import NLS.KdV.HillAbelianProductZeros

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem summable_norm_hillOmittedEnergyRootFactor_sub_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) :
    Summable (fun k : ℕ => ‖hillOmittedEnergyRootFactor q hq hr n k z-1‖) := by
  obtain ⟨N,u,hu,hbound⟩ := exists_hillOmittedEnergyRootFactor_bounded_majorant q hq hr n ‖z‖ (norm_nonneg z)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [norm_norm] using hbound k hk z le_rfl

theorem hillOmittedEnergyRootProduct_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ)
    (hz : z ∈ hillGapFilledDomain q hq hr n) :
    hillOmittedEnergyRootProduct q hq hr n z ≠ 0 := by
  have hs := summable_norm_hillOmittedEnergyRootFactor_sub_one q hq hr n z
  have he (k : ℕ) : 1+(hillOmittedEnergyRootFactor q hq hr n k z-1) =
      hillOmittedEnergyRootFactor q hq hr n k z := by ring
  have hp := tprod_one_add_ne_zero_iff
    (fun k => hillOmittedEnergyRootFactor q hq hr n k z-1) hs
  simp only [he] at hp
  apply hp.mpr
  intro k
  unfold hillOmittedEnergyRootFactor
  split_ifs with hk
  · exact one_ne_zero
  · exact div_ne_zero
      (endpointRoot_ne_zero_of_not_mem_segment _ _ z
        (not_mem_other_gap_of_mem_hillGapFilledDomain q hq hr n (k+1) (by omega) hk z hz))
      (hillGapRootEnergyFactor_denominator_ne_zero k)

theorem multipliable_hillOmittedEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) :
    Multipliable (fun k : ℕ => hillOmittedEnergyRootFactor q hq hr n k z) := by
  have hp := multipliable_one_add_of_summable
    (summable_norm_hillOmittedEnergyRootFactor_sub_one q hq hr n z)
  simpa only [add_sub_cancel] using hp

end NLS.KdV
