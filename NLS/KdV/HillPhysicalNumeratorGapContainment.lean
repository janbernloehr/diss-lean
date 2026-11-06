import NLS.KdV.HillPhysicalNumeratorGapZero
import NLS.KdV.HillHilbertRootIsolation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianHilbertRootEnergy_mem_physical_gap_of_period_zero
    (ε D : ℝ) (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n)
    (a : Coeff 2) (ha : star a = a) (hsmall : ‖a‖ < Real.pi^2/4)
    (hperiod : hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q) = 0) :
    hillAbelianHilbertRootEnergy a k ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ)
      (hillRealLabels q hq hr (2*k) : ℂ) := by
  obtain ⟨E,hE,hzero⟩ := exists_hillAbelianHilbertPsi_zero_on_physical_gap_of_period_zero
    h0q h0r ε D hc q hq hr hp n k hk a ha hperiod
  have hball := hillRealGap_mem_free_contour_ball_of_control h0q h0r ε D hc q hq hr hp k hk hE
  have he := (hillAbelianHilbertPsi_zero_iff_on_free_closedBall h0q h0r a hsmall n k hn hk hkn E
    (ball_subset_closedBall hball)).mp hzero
  exact he ▸ hE

end NLS.KdV
