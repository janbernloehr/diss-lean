import NLS.KdV.HillComplexRootSourceMatching
import NLS.KdV.HillSourceRealBandPreservation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGapContour_source_compatibility (ε D : ℝ) (hc : HillComplexPeriodControl hq hr ε D)
    (p : Coeff 2) (hp : ‖p‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    (E,p) ∈ hillL2ContinuationDomain ∧
      hillAbelianComplexRoot 0 hq hr (E,p) = hillL2ContinuedRoot (E,p) := by
  have hdom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (E,(s : ℂ) • p) ∈ hillAbelianComplexRootDomain 0 hq hr := by
    have hnorm : ‖(s : ℂ) • p‖ ≤ ‖p‖ := by
      rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg p)).trans_eq (one_mul _)
    exact (hc _ (hnorm.trans hp)).1 k hk E hE
  have hslit : E ∈ slitPlane := by
    have h := hillRealGapContour_closedBall_groundShift_slitPlane 0 hq hr k hk E
      (sphere_subset_closedBall hE)
    rw [hillRealLabels_zero_ground hq hr,ofReal_zero,sub_zero] at h
    exact h
  refine ⟨?_,hillAbelianComplexRoot_eq_continued_of_radial_domain hq hr E p hslit hdom⟩
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨hslit,?_⟩
  intro s hs
  rw [← hillAbelianComplexRoot_sq 0 hq hr _ (hdom s hs)]
  exact pow_ne_zero 2 (hillAbelianComplexRoot_ne_zero 0 hq hr _ (hdom s hs))

theorem hillFreeGapContour_physical_root_matching (ε D : ℝ) (hc : HillComplexPeriodControl hq hr ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hqp : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hqr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hsmall : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    E ∈ hillL2RealCutDomain q hqp hqr ∧
      hillAbelianComplexRoot 0 hq hr (E,SpectralWeight.one.toCoeff q) =
        hillEnergyCanonicalRootProduct q hqp hqr E := by
  have hs := hillFreeGapContour_source_compatibility hq hr ε D hc
    (SpectralWeight.one.toCoeff q) hsmall k hk E hE
  have hcut := mem_hillL2RealCutDomain_of_free_and_source hq hr q hqp hqr E
    (hillRealGapContour_sphere_subset 0 hq hr k hk hE) hs.1
  exact ⟨hcut,hs.2.trans (hillEnergyCanonicalRootProduct_eq_continued_of_mem q hqp hqr E hcut hs.1).symm⟩

theorem exists_hillFreeGapContour_physical_root_neighborhood :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hqp : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hqr : IsRealHillPotential (SpectralWeight.one.toCoeff q),
      ‖SpectralWeight.one.toCoeff q‖ ≤ ε → ∀ k : ℕ, 1 ≤ k → ∀ E : ℂ,
        E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
          (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) →
        E ∈ hillL2RealCutDomain q hqp hqr ∧
          hillAbelianComplexRoot 0 hq hr (E,SpectralWeight.one.toCoeff q) =
            hillEnergyCanonicalRootProduct q hqp hqr E := by
  obtain ⟨ε,D,hε,_,hc⟩ := exists_hillComplexPeriodControl hq hr
  exact ⟨ε,hε,fun q hqp hqr hsmall k hk E hE =>
    hillFreeGapContour_physical_root_matching hq hr ε D hc q hqp hqr hsmall k hk E hE⟩

end NLS.KdV
