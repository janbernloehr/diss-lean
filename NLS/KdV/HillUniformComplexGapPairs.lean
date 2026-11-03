import NLS.KdV.HillBoundedComplexTailDomain
import NLS.KdV.HillAllGapMultiplicities
import NLS.ComplexAnalysis.Rouche
import NLS.ComplexAnalysis.ZeroMultiset

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGapContour_bounded_complex_two_zero_count (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E ≠ 0) ∧
      analyticZeroCount (hillL2Radicand p) (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) = 2 := by
  obtain ⟨N,hN,C,hC,hbound⟩ := exists_hillFreeGapContour_bounded_complex_tail_domain h0q h0r B
  refine ⟨N,hN,?_⟩
  intro p hp k hk
  have hk1 : 1 ≤ k := hN.trans hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hlt (E : ℂ) (hE : E ∈ sphere c R) : ‖hillL2Radicand p E-hillL2Radicand 0 E‖ < ‖hillL2Radicand 0 E‖ := by
    have hRn : hillL2Radicand 0 E ≠ 0 :=
      by simpa only [map_zero] using hillL2Radicand_ne_zero_on_realCutDomain 0 h0q h0r E (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
    have hsmall := (hbound p hp k hk E hE).2.2
    have he : hillL2Radicand p E/hillL2Radicand 0 E-1 =
        (hillL2Radicand p E-hillL2Radicand 0 E)/hillL2Radicand 0 E := by field_simp
    rw [he,norm_div] at hsmall
    have hpos := norm_pos_iff.mpr hRn
    have hle := (div_le_iff₀ hpos).mp hsmall
    linarith
  have hn (E : ℂ) (hE : E ∈ sphere c R) : hillL2Radicand p E ≠ 0 :=
    (rouche_ratio_mem_slitPlane (hlt E hE)).2.1
  refine ⟨hn,?_⟩
  have hfree : analyticZeroCount (hillL2Radicand 0) (closedBall c R) = 2 := by
    simpa only [map_zero] using analyticZeroCount_hillL2Radicand_intrinsic_gap 0 h0q h0r k hk1
  exact (analyticZeroCount_eq_of_boundary_lt hR
    ((analyticOnNhd_hillL2Radicand 0).mono (subset_univ _))
    ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) hlt).trans
      hfree

theorem exists_hillFreeGapContour_bounded_complex_gap_pairs (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E := by
  obtain ⟨N,hN,hcount⟩ := exists_hillFreeGapContour_bounded_complex_two_zero_count h0q h0r B
  refine ⟨N,hN,?_⟩
  intro p hp k hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).1
    (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).2.1
  obtain ⟨hboundary,htwo⟩ := hcount p hp k hk
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have ha := (analyticOnNhd_hillL2Radicand p).mono (subset_univ (closedBall c R))
  obtain ⟨a,haK,b,hbK,haz,hbz,horders⟩ := exists_two_analytic_zeros
    (analyticZeroCount_hasFiniteSupport (isCompact_closedBall c R) (isConnected_closedBall hR.le) ha
      (sphere_subset_closedBall hz) (hboundary z hz)) htwo
  have haB : a ∈ ball c R := lt_of_le_of_ne haK (fun he => hboundary a he haz)
  have hbB : b ∈ ball c R := lt_of_le_of_ne hbK (fun he => hboundary b he hbz)
  refine ⟨hboundary,a,haB,b,hbB,haz,hbz,?_⟩
  intro E hE
  have hE' : E ∈ closedBall c R := hE
  simpa only [if_pos hE'] using horders E

end NLS.KdV
