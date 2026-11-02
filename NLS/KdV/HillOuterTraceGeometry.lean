import NLS.KdV.HillFiniteBandCover
import NLS.ComplexAnalysis.RealCenteredHoleGeometry

/-! # Actual disjoint Hill gap holes inside expanding outer circles

The outer center is fixed to the left of the lowest energy. Its right
endpoint is the midpoint of the Nth open band. Every first-N gap has a
strictly larger isolating disc around its intrinsic action circle, and
those larger discs are pairwise disjoint and enclosed by the outer circle.
-/

noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
variable (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
variable (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillRealGapOuterRadius (n : ℕ) : ℝ :=
  hillRealGapHalfLength q hq hr n + (3 / 2 : ℝ) * hillRealGapCollar q hq hr n

def hillRealOuterUpper (N : ℕ) : ℝ :=
  (hillRealLabels q hq hr (2 * N) + hillRealLabels q hq hr (2 * N + 1)) / 2

def hillRealOuterCenter : ℝ := -|hillLowestEnergy q hq hr| - 1

def hillRealOuterRadius (N : ℕ) : ℝ := hillRealOuterUpper q hq hr N - hillRealOuterCenter q hq hr

theorem hillRealOuterUpper_mem_band (N : ℕ) :
    hillRealOuterUpper q hq hr N ∈
      Ioo (hillRealLabels q hq hr (2 * N)) (hillRealLabels q hq hr (2 * N + 1)) := by
  have h := hillRealLabels_band_strict q hq hr N
  dsimp [hillRealOuterUpper]
  constructor <;> linarith

theorem hillRealOuterUpper_gt_ground (N : ℕ) :
    hillLowestEnergy q hq hr < hillRealOuterUpper q hq hr N :=
  (monotone_hillRealLabels q hq hr (Nat.zero_le (2 * N))).trans_lt
    (hillRealOuterUpper_mem_band q hq hr N).1

theorem hillRealOuterRadius_pos (N : ℕ) : 0 < hillRealOuterRadius q hq hr N := by
  have h := hillRealOuterUpper_gt_ground q hq hr N
  have habs := neg_abs_le (hillLowestEnergy q hq hr)
  dsimp [hillRealOuterRadius, hillRealOuterCenter]
  linarith

theorem hillRealGapCollar_le_bands (n : ℕ) :
    4 * hillRealGapCollar q hq hr n ≤
        hillRealLabels q hq hr (2 * n - 1) - hillRealLabels q hq hr (2 * n - 2) ∧
      4 * hillRealGapCollar q hq hr n ≤
        hillRealLabels q hq hr (2 * n + 1) - hillRealLabels q hq hr (2 * n) := by
  have hl := min_le_left
    (hillRealLabels q hq hr (2 * n - 1) - hillRealLabels q hq hr (2 * n - 2))
    (hillRealLabels q hq hr (2 * n + 1) - hillRealLabels q hq hr (2 * n))
  have hu := min_le_right
    (hillRealLabels q hq hr (2 * n - 1) - hillRealLabels q hq hr (2 * n - 2))
    (hillRealLabels q hq hr (2 * n + 1) - hillRealLabels q hq hr (2 * n))
  dsimp [hillRealGapCollar]
  constructor <;> linarith

theorem hillRealGapOuterRadius_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 < hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n ∧
      hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n < hillRealGapOuterRadius q hq hr n ∧
      hillRealGapOuterRadius q hq hr n < hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n := by
  obtain ⟨hd, hη, _⟩ := hillRealGapContour_geometry q hq hr n hn
  dsimp [hillRealGapOuterRadius]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem hillRealGapOuter_endpoints (n : ℕ) (hn : 1 ≤ n) :
    hillRealLabels q hq hr (2 * n - 2) < hillRealGapCenter q hq hr n - hillRealGapOuterRadius q hq hr n ∧
      hillRealGapCenter q hq hr n + hillRealGapOuterRadius q hq hr n < hillRealLabels q hq hr (2 * n + 1) := by
  obtain ⟨_, _, hl, hu, _⟩ := hillRealGapContour_geometry q hq hr n hn
  have hc := hillRealGapCollar_le_bands q hq hr n
  have hprev := hillRealLabels_band_strict q hq hr (n - 1)
  rw [show 2 * (n - 1) = 2 * n - 2 by omega,
    show 2 * n - 2 + 1 = 2 * n - 1 by omega] at hprev
  have hnext := hillRealLabels_band_strict q hq hr n
  dsimp [hillRealGapOuterRadius]
  constructor <;> linarith [hc.1, hc.2]

theorem hillRealGapOuter_separated (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i < j) :
    hillRealGapCenter q hq hr i + hillRealGapOuterRadius q hq hr i <
      hillRealGapCenter q hq hr j - hillRealGapOuterRadius q hq hr j := by
  obtain ⟨_, _, _, hiR, _⟩ := hillRealGapContour_geometry q hq hr i hi
  obtain ⟨_, _, hjL, _, _⟩ := hillRealGapContour_geometry q hq hr j hj
  have hband := hillRealLabels_band_strict q hq hr i
  have horder₁ := monotone_hillRealLabels q hq hr (show 2 * i + 1 ≤ 2 * j - 1 by omega)
  have horder₂ := monotone_hillRealLabels q hq hr (show 2 * i ≤ 2 * j - 2 by omega)
  have hc₁ := (hillRealGapCollar_le_bands q hq hr i).2
  have hc₂ := (hillRealGapCollar_le_bands q hq hr j).1
  dsimp [hillRealGapOuterRadius]
  linarith

theorem hillRealGapOuter_disjoint (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
    Disjoint (closedBall (hillRealGapCenter q hq hr i : ℂ) (hillRealGapOuterRadius q hq hr i))
      (closedBall (hillRealGapCenter q hq hr j : ℂ) (hillRealGapOuterRadius q hq hr j)) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact real_closedBalls_disjoint_of_separated _ _ _ _ (hillRealGapOuter_separated q hq hr i j hi hj hij)
  · exact (real_closedBalls_disjoint_of_separated _ _ _ _
      (hillRealGapOuter_separated q hq hr j i hj hi hji)).symm

theorem hillRealGapOuter_enclosed (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    closedBall (hillRealGapCenter q hq hr n : ℂ) (hillRealGapOuterRadius q hq hr n) ⊆
      ball (hillRealOuterCenter q hq hr : ℂ) (hillRealOuterRadius q hq hr N) := by
  let U := hillRealOuterUpper q hq hr N
  let c := hillRealOuterCenter q hq hr
  let L := 2 * c - U
  have hU : hillLowestEnergy q hq hr < U := hillRealOuterUpper_gt_ground q hq hr N
  have hL : L < hillLowestEnergy q hq hr := by
    have habs := neg_abs_le (hillLowestEnergy q hq hr)
    dsimp [L, c, hillRealOuterCenter]
    linarith
  have hleft : L < hillRealGapCenter q hq hr n - hillRealGapOuterRadius q hq hr n :=
    hL.trans ((monotone_hillRealLabels q hq hr (Nat.zero_le (2 * n - 2))).trans_lt
      (hillRealGapOuter_endpoints q hq hr n hn).1)
  have hright : hillRealGapCenter q hq hr n + hillRealGapOuterRadius q hq hr n < U := by
    rcases lt_or_eq_of_le hnN with hlt | rfl
    · have ho := monotone_hillRealLabels q hq hr (show 2 * n + 1 ≤ 2 * N by omega)
      exact ((hillRealGapOuter_endpoints q hq hr n hn).2.trans_le ho).trans
        (hillRealOuterUpper_mem_band q hq hr N).1
    · obtain ⟨_, _, _, hcenter, _⟩ := hillRealGapContour_geometry q hq hr n hn
      have hc := (hillRealGapCollar_le_bands q hq hr n).2
      have hb := hillRealLabels_band_strict q hq hr n
      dsimp [hillRealGapOuterRadius, U, hillRealOuterUpper]
      linarith
  have hcenter : (L + U) / 2 = c := by dsimp [L]; ring
  have hradius : (U - L) / 2 = hillRealOuterRadius q hq hr N := by
    dsimp [L, hillRealOuterRadius, U, c]
    ring
  simpa only [hcenter, hradius] using real_closedBall_subset_diameter_ball _ _ L U hleft hright

end NLS.KdV
