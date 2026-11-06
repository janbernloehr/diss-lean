import NLS.KdV.HillFrequencyPhysicalPeriodTransfer
import NLS.KdV.HillFreeGapContourGeometry
/-! # Canonical physical root matching on radius-k free energy circles

These circles lie in the full free cut domain, including the first one.
Actual source continuation and indexed band preservation then identify
the rough/L2 sheet with the canonical physical root at real sources.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

theorem hillRadiusEnergyCircle_subset_freeCut (k : ℕ+) (E : ℂ)
    (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : E ∈ hillL2RealCutDomain 0 h0q h0r := by
  have hfr : (freeHillValue (k : ℕ) : ℂ) = freeHillEnergy k := by
    dsimp only [freeHillValue,freeHillEnergy]
    push_cast
    ring
  have hc : (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) = freeHillEnergy k := by
    rw [hillFreeGapCenter h0q h0r (k : ℕ) k.property,hfr]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hR : (k : ℝ) ≤ hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ) := by
    rw [hillFreeGapHalfLength h0q h0r (k : ℕ) k.property,zero_add,hillFreeGapCollar h0q h0r (k : ℕ) k.property]
    have hh := mul_nonneg (show 0 ≤ Real.pi^2-4 by nlinarith [Real.pi_gt_three])
      (show 0 ≤ 2*(k : ℝ)-1 by linarith)
    nlinarith
  apply mem_hillL2RealCutDomain_of_filled_not_gap 0 h0q h0r (k : ℕ) k.property E
  · apply hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r (k : ℕ) k.property
    rw [hc]
    exact closedBall_subset_closedBall hR (sphere_subset_closedBall hE)
  · obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r (k : ℕ) k.property
    rw [hl,hu,segment_same,hfr]
    intro he
    have hh := mem_sphere_iff_norm.mp hE
    simp only [mem_singleton_iff] at he
    rw [he,sub_self,norm_zero] at hh
    linarith

theorem hillRadiusEnergyCircle_actual_physical_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (u : Coeff 2) (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (k : ℕ+) (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ))
    (ht : (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain) :
    E ∈ hillL2RealCutDomain q hq hr ∧
      hillHminusContinuedRoot (E,periodOneL2Inclusion u) = hillEnergyCanonicalRootProduct q hq hr E := by
  have hL := (hillHminusContinuationDomain_L2_iff E u).mp ht
  have hLs : (E,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by rw [hcoeff];exact hL
  have hcut := mem_hillL2RealCutDomain_of_free_and_source h0q h0r q hq hr E
    (hillRadiusEnergyCircle_subset_freeCut h0q h0r k E hE) hLs
  refine ⟨hcut,?_⟩
  rw [hillHminusContinuedRoot_eq_hillL2 E u hL,← hcoeff]
  exact (hillEnergyCanonicalRootProduct_eq_continued_of_mem q hq hr E hcut hLs).symm
end NLS.KdV
