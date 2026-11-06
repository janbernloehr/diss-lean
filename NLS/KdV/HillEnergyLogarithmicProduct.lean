import NLS.KdV.HillCriticalEnergyZeros
import NLS.KdV.HillEnergyRootIdentification

/-! # The actual logarithmic differential is the literal energy critical/root ratio product. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
open NLS.ComplexAnalysis
namespace NLS.KdV
def hillEnergyCriticalRootRatio
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  ((hillGapCriticalPoint q hq hr n : ℂ)-z)/
    endpointRoot (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) z

theorem hillEnergyCriticalRootRatio_eq_factor_div
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    hillEnergyCriticalRootRatio q hq hr n z = hillEnergyCriticalFactor q hq hr n z / hillEnergyRootFactor q hq hr n z := by
  have hd : (freeHillValue n : ℂ) ≠ 0 := by
    apply ofReal_ne_zero.mpr
    unfold freeHillValue
    exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ (by exact_mod_cast (show (n : ℤ) ≠ 0 by omega)))
  unfold hillEnergyCriticalRootRatio hillEnergyCriticalFactor hillEnergyRootFactor
  exact (div_div_div_cancel_right₀ hd _ _).symm

theorem hasProd_hillEnergyCriticalRootRatio
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    HasProd (fun k : ℕ => hillEnergyCriticalRootRatio q hq hr (k+1) z)
      (hillEnergyCriticalProduct q hq hr z / hillEnergyRootProduct q hq hr z) := by
  have hn := hillEnergyRootProduct_ne_zero q hq hr z
    (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr z hz)
  have h := (multipliable_hillEnergyCriticalFactors q hq hr z).hasProd.div₀
    (multipliable_hillEnergyRootFactors q hq hr z).hasProd hn
  have he (k : ℕ) := hillEnergyCriticalRootRatio_eq_factor_div q hq hr (k+1) (by omega) z
  simp only [he]
  convert! h using 1

theorem hillL2LogarithmicDifferential_energyProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
      hillEnergyCanonicalRootProduct q hq hr z =
      1/(2*I*Complex.sqrt (z-hillRealLabels q hq hr 0)) *
        ∏' k : ℕ, hillEnergyCriticalRootRatio q hq hr (k+1) z := by
  rw [(hasProd_hillEnergyCriticalRootRatio q hq hr z hz).tprod_eq,
    hillL2Discriminant_derivative_eq_energyCriticalProduct q hq hr z,hillEnergyCanonicalRootProduct]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_neg]
  ring


end NLS.KdV
