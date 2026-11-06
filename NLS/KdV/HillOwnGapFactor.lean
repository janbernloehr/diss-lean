import NLS.KdV.HillClosedGapAbelianCorrections
import NLS.KdV.HillSpectralCartesian

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillOwnGapFactor (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  (hillRealGapCenter q hq hr n : ℂ)-(hillDirichletEnergy q hq hr n hn : ℂ)+
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)/
      hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn)

theorem hillOwnGapFactor_closed (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealGapHalfLength q hq hr n = 0) : hillOwnGapFactor q hq hr n hn = 0 := by
  have hab : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n) := by
    unfold hillRealGapHalfLength at hc
    linarith
  have hmem := hillDirichletEnergy_mem_gap q hq hr n hn
  have hμ : hillDirichletEnergy q hq hr n hn = hillRealLabels q hq hr (2*n-1) := by linarith [hmem.1,hmem.2]
  have hτ : hillRealGapCenter q hq hr n = hillRealLabels q hq hr (2*n-1) := by
    dsimp only [hillRealGapCenter]
    rw [← hab]
    ring
  rw [hillOwnGapFactor,hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr n hn hc,hμ,hτ,
    sub_self,zero_div,add_zero]

theorem hillOwnGapFactor_eq_halfLength_mul_phase (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    hillOwnGapFactor q hq hr n hn = (hillRealGapHalfLength q hq hr n : ℂ)*hillDirichletCirclePhase q hq hr n hn := by
  have hδ : (hillRealGapHalfLength q hq hr n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hgap
  have hμmem := hillGapSegment_subset_filledDomain q hq hr n hn
    (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega)) (hillDirichletEnergy_mem_gap q hq hr n hn))
  have hU := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr n hn _ hμmem
  unfold hillOwnGapFactor hillDirichletCirclePhase hillDirichletGapCosine hillDirichletGapSine
  field_simp
  simp only [I_sq]
  ring

end NLS.KdV
