import NLS.KdV.HillAllGapMultiplicities
import NLS.ComplexAnalysis.RealSimpleZeroSigns

/-! # Actual Hill trace derivatives at both endpoints of every open gap

The checked all-index multiplicity formula makes each endpoint a simple
radicand zero. Consequently the original energy discriminant has nonzero
derivative there, without a high-index or finite-gap restriction.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem deriv_hillL2Discriminant_ne_zero_open_gap_endpoint
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) (E : ℂ)
    (hE : E = (hillRealLabels q hq hr (2*k-1) : ℂ) ∨ E = (hillRealLabels q hq hr (2*k) : ℂ)) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) E ≠ 0 := by
  have hab : (hillRealLabels q hq hr (2*k-1) : ℂ) ≠ (hillRealLabels q hq hr (2*k) : ℂ) := by
    intro he
    apply hgap
    dsimp only [hillRealGapHalfLength]
    rw [Complex.ofReal_injective he]
    simp only [sub_self,zero_div]
  have hseg : E ∈ segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) := by
    rcases hE with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hdom := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
    (ball_subset_closedBall (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk hseg))
  have ho : analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) E = 1 := by
    rw [analyticOrderNatAt_hillL2Radicand_in_filled_gap q hq hr k hk E hdom]
    rcases hE with rfl | rfl <;> simp [hab,Ne.symm hab]
  have hrad := deriv_ne_zero_of_analyticOrderNatAt_eq_one _ E
    (analyticOnNhd_hillL2Radicand _ E (mem_univ _)) ho
  intro hd
  have ht := ((analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) E (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const 4
  have heq : (fun x : ℂ => (hillL2Discriminant (SpectralWeight.one.toCoeff q)^2) x-4) =
      hillL2Radicand (SpectralWeight.one.toCoeff q) := by funext x;rfl
  rw [heq] at ht
  apply hrad
  simpa only [hd,mul_zero] using ht.deriv

end NLS.KdV
