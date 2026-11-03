import NLS.KdV.HillFilledGapCutDomain
import NLS.KdV.HillLabelContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q0 : WeightedCoeff SpectralWeight.one.toWeight 2)
    (h0q : SpectralWeight.one.toCoeff q0 ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff q0))

theorem exists_hillIntrinsicContour_local_physical_geometry (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V,
        (hillRealLabels p.val p.property.1 p.property.2 (2*k-2) < hillRealGapCenter q0 h0q h0r k-
          (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) ∧
        hillRealGapCenter q0 h0q h0r k+(hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) <
          hillRealLabels p.val p.property.1 p.property.2 (2*k+1)) ∧
        segment ℝ (hillRealLabels p.val p.property.1 p.property.2 (2*k-1) : ℂ)
          (hillRealLabels p.val p.property.1 p.property.2 (2*k) : ℂ) ⊆
          ball (hillRealGapCenter q0 h0q h0r k : ℂ)
            (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) := by
  let c := hillRealGapCenter q0 h0q h0r k
  let R := hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k
  let V : Set RealPeriodOneHillPotential := {p |
    (hillRealLabels p.val p.property.1 p.property.2 (2*k-2) < c-R ∧
      c+R < hillRealLabels p.val p.property.1 p.property.2 (2*k+1)) ∧
    (hillRealLabels p.val p.property.1 p.property.2 (2*k-1) : ℂ) ∈ ball (c : ℂ) R ∧
    (hillRealLabels p.val p.property.1 p.property.2 (2*k) : ℂ) ∈ ball (c : ℂ) R}
  have hV : IsOpen V :=
    ((isOpen_lt (continuous_hillRealLabels (2*k-2)) continuous_const).inter
      (isOpen_lt continuous_const (continuous_hillRealLabels (2*k+1)))).inter
        (((isOpen_ball.preimage (continuous_ofReal.comp (continuous_hillRealLabels (2*k-1))))).inter
          (isOpen_ball.preimage (continuous_ofReal.comp (continuous_hillRealLabels (2*k)))))
  have hqV : (⟨q0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ V := by
    refine ⟨hillRealGapContour_band_bounds q0 h0q h0r k hk,?_,?_⟩
    · apply hillRealGapSegment_subset_intrinsic_contour_ball q0 h0q h0r k hk
      exact left_mem_segment ℝ _ _
    · apply hillRealGapSegment_subset_intrinsic_contour_ball q0 h0q h0r k hk
      exact right_mem_segment ℝ _ _
  refine ⟨V,hV,hqV,?_⟩
  intro p hp
  exact ⟨hp.1,(convex_ball _ _).segment_subset hp.2.1 hp.2.2⟩

end NLS.KdV
