import NLS.KdV.HillOmittedEnergyCriticalProduct
import NLS.KdV.HillRealGapContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillRealGapContour_band_bounds (n : ℕ) (hn : 1 ≤ n) :
    hillRealLabels q hq hr (2*n-2) < hillRealGapCenter q hq hr n -
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ∧
    hillRealGapCenter q hq hr n +
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) <
      hillRealLabels q hq hr (2*n+1) := by
  have hlo := hillRealLabels_band_strict q hq hr (n-1)
  have hi0 : 2*(n-1) = 2*n-2 := by omega
  have hi1 : 2*n-2+1 = 2*n-1 := by omega
  rw [hi0,hi1] at hlo
  have hup := hillRealLabels_band_strict q hq hr n
  have hm0 := min_le_left
    (hillRealLabels q hq hr (2*n-1)-hillRealLabels q hq hr (2*n-2))
    (hillRealLabels q hq hr (2*n+1)-hillRealLabels q hq hr (2*n))
  have hm1 := min_le_right
    (hillRealLabels q hq hr (2*n-1)-hillRealLabels q hq hr (2*n-2))
    (hillRealLabels q hq hr (2*n+1)-hillRealLabels q hq hr (2*n))
  dsimp only [hillRealGapCenter,hillRealGapHalfLength,hillRealGapCollar]
  constructor <;> linarith

theorem hillRealGapContour_closedBall_real_bounds (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ closedBall (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) :
    hillRealLabels q hq hr (2*n-2) < z.re ∧
      z.re < hillRealLabels q hq hr (2*n+1) := by
  have hb := hillRealGapContour_band_bounds q hq hr n hn
  have hd : ‖z-(hillRealGapCenter q hq hr n : ℂ)‖ ≤
      hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre := abs_le.mp ((abs_re_le_norm (z-(hillRealGapCenter q hq hr n : ℂ))).trans hd)
  simp only [sub_re,ofReal_re] at hre
  exact ⟨by linarith [hb.1,hre.1],by linarith [hb.2,hre.2]⟩

theorem hillRealGapContour_closedBall_subset_filledDomain (n : ℕ) (hn : 1 ≤ n) :
    closedBall (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ⊆
        hillGapFilledDomain q hq hr n := by
  intro z hz
  exact Or.inr (hillRealGapContour_closedBall_real_bounds q hq hr n hn z hz)

theorem hillRealGapContour_closedBall_groundShift_slitPlane (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ closedBall (hillRealGapCenter q hq hr n : ℂ)
      (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n)) :
    z-(hillRealLabels q hq hr 0 : ℂ) ∈ slitPlane :=
  hillGroundShift_mem_slitPlane_of_mem_filledDomain q hq hr n z
    (hillRealGapContour_closedBall_subset_filledDomain q hq hr n hn hz)

end NLS.KdV
