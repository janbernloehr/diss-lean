import NLS.KdV.HillHighFreeContourBandBounds
import NLS.ComplexAnalysis.EndpointRootDiscBounds
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

/-! # High free discs contain the physical gap and support deflated analytic bounds -/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHighFreeContour_closedBall_subset_filledDomain
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (q : RealPeriodOneHillPotential) (hq : ‖SpectralWeight.one.toCoeff q.val‖ ≤ B)
    (k : ℕ) (hk : N ≤ k) :
    closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ⊆
        hillGapFilledDomain q.val q.property.1 q.property.2 k := by
  intro z hz
  have hb := hillHighFreeContour_physical_band_bounds_of_control h0q h0r N hN B D hc
    q.val q.property.1 q.property.2 hq k hk
  have hre := re_bounds_of_mem_realCenteredClosedBall hz
  exact Or.inr ⟨by linarith [hb.1,hre.1],by linarith [hb.2,hre.2]⟩

theorem norm_hillHighFreeContour_endpointRoot_le
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (q : RealPeriodOneHillPotential) (hq : ‖SpectralWeight.one.toCoeff q.val‖ ≤ B)
    (k : ℕ) (hk : N ≤ k) (z : ℂ)
    (hz : z ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    ‖endpointRoot (hillRealLabels q.val q.property.1 q.property.2 (2*k-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*k)) z‖ ≤ (k : ℝ)*Real.pi^2 := by
  have hk1 : 1 ≤ k := hN.trans hk
  have hseg := hillRealGap_mem_high_free_contour_ball_of_control h0q h0r N hN B D hc
    q.val q.property.1 q.property.2 hq k hk
  have hrad := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hb := norm_endpointRoot_le_twice_radius
    (hillRealLabels q.val q.property.1 q.property.2 (2*k-1))
    (hillRealLabels q.val q.property.1 q.property.2 (2*k))
    (hillRealGapCenter 0 h0q h0r k) z _ hrad.le
    (ball_subset_closedBall (hseg (left_mem_segment ℝ _ _)))
    (ball_subset_closedBall (hseg (right_mem_segment ℝ _ _))) hz
    (fun hs => sphere_disjoint_ball.le_bot ⟨hz,hseg hs⟩)
  apply hb.trans
  rw [hillFreeGapHalfLength h0q h0r k hk1,zero_add,hillFreeGapCollar h0q h0r k hk1]
  nlinarith [sq_nonneg Real.pi]

end NLS.KdV
