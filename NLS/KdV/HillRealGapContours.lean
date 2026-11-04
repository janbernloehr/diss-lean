import NLS.KdV.HillL2CutBounds
import NLS.ComplexAnalysis.RealGapDiscIsolation

/-! # Intrinsic isolating circles for every real Hill gap

The gap midpoint and a quarter of the smaller neighboring band length
give canonical inner and outer circles. No high-index restriction or
positive gap length is required.
-/

noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

def hillRealGapCenter
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  (hillRealLabels q hq hr (2 * n - 1) + hillRealLabels q hq hr (2 * n)) / 2

def hillRealGapHalfLength
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  (hillRealLabels q hq hr (2 * n) - hillRealLabels q hq hr (2 * n - 1)) / 2

def hillRealGapCollar
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  min (hillRealLabels q hq hr (2 * n - 1) - hillRealLabels q hq hr (2 * n - 2))
    (hillRealLabels q hq hr (2 * n + 1) - hillRealLabels q hq hr (2 * n)) / 4

theorem hillRealGapContour_geometry
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ hillRealGapHalfLength q hq hr n ∧ 0 < hillRealGapCollar q hq hr n ∧
      hillRealGapCenter q hq hr n - hillRealGapHalfLength q hq hr n = hillRealLabels q hq hr (2 * n - 1) ∧
      hillRealGapCenter q hq hr n + hillRealGapHalfLength q hq hr n = hillRealLabels q hq hr (2 * n) ∧
      ball (hillRealGapCenter q hq hr n : ℂ)
          (hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n) \
        segment ℝ (hillRealLabels q hq hr (2 * n - 1) : ℂ) (hillRealLabels q hq hr (2 * n)) ⊆
          hillL2RealCutDomain q hq hr := by
  let l := hillRealLabels q hq hr (2 * n - 2)
  let a := hillRealLabels q hq hr (2 * n - 1)
  let b := hillRealLabels q hq hr (2 * n)
  let u := hillRealLabels q hq hr (2 * n + 1)
  have hla : l < a := by
    simpa only [show 2 * (n - 1) = 2 * n - 2 by omega,
      show 2 * n - 2 + 1 = 2 * n - 1 by omega] using hillRealLabels_band_strict q hq hr (n - 1)
  have hab : a ≤ b := monotone_hillRealLabels q hq hr (by omega)
  have hbu : b < u := hillRealLabels_band_strict q hq hr n
  have hmin : 0 < min (a - l) (u - b) := lt_min (by linarith) (by linarith)
  have hcollar : 0 < hillRealGapCollar q hq hr n := div_pos hmin (by norm_num)
  refine ⟨by dsimp [hillRealGapHalfLength]; linarith, hcollar, ?_, ?_, ?_⟩
  · dsimp [hillRealGapCenter, hillRealGapHalfLength]; ring
  · dsimp [hillRealGapCenter, hillRealGapHalfLength]; ring
  · intro z hz
    have hl : l < hillRealGapCenter q hq hr n -
        (hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n) := by
      have hm := min_le_left (a - l) (u - b)
      dsimp [hillRealGapCenter, hillRealGapHalfLength, hillRealGapCollar]
      change l < (a + b) / 2 - ((b - a) / 2 + 2 * (min (a - l) (u - b) / 4))
      linarith
    have hu : hillRealGapCenter q hq hr n +
        (hillRealGapHalfLength q hq hr n + 2 * hillRealGapCollar q hq hr n) < u := by
      have hm := min_le_right (a - l) (u - b)
      change (a + b) / 2 + ((b - a) / 2 + 2 * (min (a - l) (u - b) / 4)) < u
      linarith
    rcases real_gap_disc_exterior_band l a b u _ _ hab hl hu z hz with hi | hlband | huband
    · exact Or.inl hi
    · refine Or.inr ⟨n - 1, ?_⟩
      simpa only [show 2 * (n - 1) = 2 * n - 2 by omega,
        show 2 * n - 2 + 1 = 2 * n - 1 by omega] using hlband
    · exact Or.inr ⟨n, huband⟩

theorem hillRealGapContour_sphere_subset
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    sphere (hillRealGapCenter q hq hr n : ℂ)
        (hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n) ⊆ hillL2RealCutDomain q hq hr := by
  obtain ⟨hd, hη, hl, hu, hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  let c := hillRealGapCenter q hq hr n
  let d := hillRealGapHalfLength q hq hr n
  let η := hillRealGapCollar q hq hr n
  have hcut : segment ℝ (hillRealLabels q hq hr (2 * n - 1) : ℂ)
      (hillRealLabels q hq hr (2 * n)) ⊆ ball (c : ℂ) (d + η) := by
    apply (convex_ball _ _).segment_subset
    · rw [← hl]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      change |c - d - c| < d + η
      rw [show c - d - c = -d by ring, abs_neg, abs_of_nonneg hd]
      linarith
    · rw [← hu]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      change |c + d - c| < d + η
      rw [show c + d - c = d by ring, abs_of_nonneg hd]
      linarith
  intro z hz
  apply hsub
  refine ⟨?_, fun hk => (sphere_disjoint_ball : Disjoint (sphere (c : ℂ) (d + η)) (ball (c : ℂ) (d + η))).le_bot ⟨hz, hcut hk⟩⟩
  rw [mem_ball, mem_sphere.mp hz]
  linarith

end NLS.KdV
