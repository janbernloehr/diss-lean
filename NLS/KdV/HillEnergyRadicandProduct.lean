import NLS.KdV.HillEnergyEndpointLabeling
import NLS.KdV.HillEnergyRootAnalytic

/-! # The actual energy periodic product converges to the Hill radicand, and the normalized energy root product squares to it on the cut domain. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem tendsto_hillEnergyPeriodicPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Tendsto (hillEnergyPeriodicPartialProduct q hq hr z) atTop
      (𝓝 (hillL2Radicand (SpectralWeight.one.toCoeff q) z)) := by
  have hs : (Complex.sqrt z)^2 = z := by
    have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have h := (tendstoLocallyUniformlyOn_entireSpectralPairProduct
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) _ _
    (memℓp_hillSignedEnergyRoot_displacement q hq hr false)
    (memℓp_hillSignedEnergyRoot_displacement q hq hr true)).tendsto_at (Set.mem_univ (Complex.sqrt z))
  simp only [spectralPairPartialProduct_hillSignedEnergyRoot,hs] at h
  rw [entireSpectralPairProduct_hillSignedEnergyRoot q hq hr,
    canonicalPeriodic_eq_discriminant_sq_sub_four _ (hillL2CoefficientPotential_even _),
    canonicalDiscriminant_hillL2CoefficientPotential,hs] at h
  exact h

theorem hillEnergyCanonicalRootPartialProduct_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) (N : ℕ) :
    hillEnergyCanonicalRootPartialProduct q hq hr z N ^2 =
      hillEnergyPeriodicPartialProduct q hq hr z N := by
  have hs : (Complex.sqrt (z-hillRealLabels q hq hr 0))^2 = z-hillRealLabels q hq hr 0 := by
    have h := Complex.cpow_nat_inv_pow (z-hillRealLabels q hq hr 0) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hf (k : ℕ) := hillEnergyRootFactor_sq q hq hr (k+1) z
    (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr z hz (k+1) (by omega))
  simp only [Nat.cast_add,Nat.cast_one] at hf
  simp only [hillEnergyCanonicalRootPartialProduct,mul_pow,hs,← Finset.prod_pow,hf,
    hillEnergyPeriodicPartialProduct,I_sq]
  ring

theorem hillEnergyCanonicalRootProduct_sq_eq_radicand
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillEnergyCanonicalRootProduct q hq hr z ^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z := by
  apply tendsto_nhds_unique ((tendsto_hillEnergyCanonicalRootPartialProduct q hq hr z).pow 2)
  simpa only [hillEnergyCanonicalRootPartialProduct_sq q hq hr z hz] using
    tendsto_hillEnergyPeriodicPartialProduct q hq hr z


end NLS.KdV
