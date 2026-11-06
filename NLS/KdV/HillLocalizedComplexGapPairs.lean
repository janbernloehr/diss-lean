import NLS.KdV.HillScaledComplexZeroCounts
import NLS.KdV.HillUniformComplexGapPairs
import NLS.ComplexAnalysis.EqualZeroCountRestriction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_localized_pairs
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
      ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
        hillL2Radicand p a=0 ∧ hillL2Radicand p b=0 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          analyticOrderNatAt (hillL2Radicand p) E=({a,b} : Multiset ℂ).count E := by
  obtain ⟨Ni,hNi,hinner⟩ := exists_hillScaledFreeGapContour_bounded_complex_zero_counts h0q h0r ρ hρ hρ1 B
  obtain ⟨No,hNo,houter⟩ := exists_hillFreeGapContour_bounded_complex_two_zero_count h0q h0r B
  refine ⟨max Ni No,hNi.trans (le_max_left _ _),?_⟩
  intro p hp k hk
  have hki : Ni ≤ k := (le_max_left _ _).trans hk
  have hko : No ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNi.trans hki
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hbi,hci⟩ := (hinner p hp k hki).1
  obtain ⟨hbo,hco⟩ := houter p hp k hko
  have hsub : closedBall c (ρ*R) ⊆ closedBall c R := closedBall_subset_closedBall (mul_le_of_le_one_left hR.le hρ1)
  have ha := (analyticOnNhd_hillL2Radicand p).mono (subset_univ (closedBall c R))
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have hfin := analyticZeroCount_hasFiniteSupport (isCompact_closedBall c R) (isConnected_closedBall hR.le) ha
    (sphere_subset_closedBall hw) (hbo w hw)
  have heq := analyticOrder_indicator_eq_of_subset_equal_count (hillL2Radicand p) hsub hfin (hci.trans hco.symm)
  obtain ⟨a,haK,b,hbK,haz,hbz,hm⟩ := exists_two_analytic_zeros
    (hasFiniteSupport_analyticOrder_subset (hillL2Radicand p) hsub hfin) hci
  have haB : a ∈ ball c (ρ*R) := lt_of_le_of_ne haK (fun he => hbi a he haz)
  have hbB : b ∈ ball c (ρ*R) := lt_of_le_of_ne hbK (fun he => hbi b he hbz)
  refine ⟨hbo,a,haB,b,hbB,haz,hbz,?_⟩
  intro E hE
  have hE' : E ∈ closedBall c R := hE
  have hh := heq E
  rw [if_pos hE'] at hh
  exact hh.symm.trans (hm E)

end NLS.KdV
