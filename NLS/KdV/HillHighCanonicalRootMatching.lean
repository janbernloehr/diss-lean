import NLS.KdV.HillComplexTailPeriodAnalytic
import NLS.KdV.HillFreeContourPhysicalBandBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHighFreeGapContour_source_compatibility (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (p : Coeff 2) (hp : ‖p‖ ≤ B) (k : ℕ) (hk : N ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    (E,p) ∈ hillL2ContinuationDomain ∧
      hillAbelianComplexRoot 0 h0q h0r (E,p) = hillL2ContinuedRoot (E,p) := by
  have hk1 : 1 ≤ k := hN.trans hk
  have hdom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (E,(s : ℂ) • p) ∈ hillAbelianComplexRootDomain 0 h0q h0r := by
    have hnorm : ‖(s : ℂ) • p‖ ≤ ‖p‖ := by
      rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg p)).trans_eq (one_mul _)
    exact (hc _ (hnorm.trans hp)).1 k hk E hE
  have hslit : E ∈ slitPlane := by
    have h := hillRealGapContour_closedBall_groundShift_slitPlane 0 h0q h0r k hk1 E
      (sphere_subset_closedBall hE)
    rw [hillRealLabels_zero_ground h0q h0r,ofReal_zero,sub_zero] at h
    exact h
  refine ⟨?_,hillAbelianComplexRoot_eq_continued_of_radial_domain h0q h0r E p hslit hdom⟩
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨hslit,?_⟩
  intro s hs
  rw [← hillAbelianComplexRoot_sq 0 h0q h0r _ (hdom s hs)]
  exact pow_ne_zero 2 (hillAbelianComplexRoot_ne_zero 0 h0q h0r _ (hdom s hs))

theorem hillHighFreeGapContour_physical_root_matching (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hqp : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hqr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hsmall : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (k : ℕ) (hk : N ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    E ∈ hillL2RealCutDomain q hqp hqr ∧
      hillAbelianComplexRoot 0 h0q h0r (E,SpectralWeight.one.toCoeff q) =
        hillEnergyCanonicalRootProduct q hqp hqr E := by
  have hk1 : 1 ≤ k := hN.trans hk
  have hs := hillHighFreeGapContour_source_compatibility h0q h0r N hN B D hc
    (SpectralWeight.one.toCoeff q) hsmall k hk E hE
  have hcut := mem_hillL2RealCutDomain_of_free_and_source h0q h0r q hqp hqr E
    (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE) hs.1
  exact ⟨hcut,hs.2.trans (hillEnergyCanonicalRootProduct_eq_continued_of_mem q hqp hqr E hcut hs.1).symm⟩

end NLS.KdV
