import NLS.KdV.HillAllGapSymmetricData
import NLS.KdV.HillLocalContourGeometry
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q0 : WeightedCoeff SpectralWeight.one.toWeight 2)
    (h0q : SpectralWeight.one.toCoeff q0 ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff q0))

theorem hillLocalGapSymmetricData_eq_physical_of_geometry
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k)
    (hband : hillRealLabels q hq hr (2*k-2) < hillRealGapCenter q0 h0q h0r k-
        (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) ∧
      hillRealGapCenter q0 h0q h0r k+(hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) <
        hillRealLabels q hq hr (2*k+1))
    (hgap : segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆
      ball (hillRealGapCenter q0 h0q h0r k : ℂ)
        (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k)) :
    hillLocalGapMidpoint q0 h0q h0r k (SpectralWeight.one.toCoeff q) =
      (hillRealGapCenter q hq hr k : ℂ) ∧
    hillLocalGapSquare q0 h0q h0r k (SpectralWeight.one.toCoeff q) =
      (2*(hillRealGapHalfLength q hq hr k : ℂ))^2 := by
  let c : ℂ := hillRealGapCenter q0 h0q h0r k
  let R := hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k
  have hfilled (z : ℂ) (hz : z ∈ closedBall c R) : z ∈ hillGapFilledDomain q hq hr k := by
    have hre := re_bounds_of_mem_realCenteredClosedBall hz
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  have hb (z : ℂ) (hz : z ∈ sphere c R) : hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 := by
    have hn : z ∉ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) :=
      fun hm => (ne_of_lt (hgap hm)) hz
    exact hillL2Radicand_ne_zero_on_realCutDomain q hq hr z
      (mem_hillL2RealCutDomain_of_filled_not_gap q hq hr k hk z
        (hfilled z (sphere_subset_closedBall hz)) hn)
  have hm (z : ℂ) (hz : z ∈ closedBall c R) :=
    analyticOrderNatAt_hillL2Radicand_in_filled_gap q hq hr k hk z (hfilled z hz)
  have hs := hillLocalGapSymmetricData_eq_of_pair q0 h0q h0r k hk (SpectralWeight.one.toCoeff q)
    hb (hgap (left_mem_segment ℝ _ _)) (hgap (right_mem_segment ℝ _ _)) hm
  constructor
  · convert hs.1 using 1
    simp [hillRealGapCenter]
  · convert hs.2 using 1
    simp only [hillRealGapHalfLength, ofReal_div, ofReal_sub, ofReal_ofNat]
    ring

theorem exists_hillLocalGapSymmetricData_physical_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Set RealPeriodOneHillPotential, IsOpen W ∧
      (⟨q0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ W ∧
      ∀ p ∈ W,
        hillLocalGapMidpoint q0 h0q h0r k (SpectralWeight.one.toCoeff p.val) =
          (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ) ∧
        hillLocalGapSquare q0 h0q h0r k (SpectralWeight.one.toCoeff p.val) =
          (2*(hillRealGapHalfLength p.val p.property.1 p.property.2 k : ℂ))^2 := by
  obtain ⟨W,hW,hqW,hgeo⟩ := exists_hillIntrinsicContour_local_physical_geometry q0 h0q h0r k hk
  refine ⟨W,hW,hqW,?_⟩
  intro p hp
  exact hillLocalGapSymmetricData_eq_physical_of_geometry q0 h0q h0r
    p.val p.property.1 p.property.2 k hk (hgeo p hp).1 (hgeo p hp).2

end NLS.KdV
