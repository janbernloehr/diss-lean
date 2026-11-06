import NLS.KdV.HillOuterTraceGeometry
import NLS.KdV.HillL2BandAnchors

/-! # Enclosing the actual Hill gap holes by free half-lattice energy circles -/

noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
variable (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
variable (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillRealGapOuter_last_lt_free_energy (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    hillRealGapCenter q hq hr N + hillRealGapOuterRadius q hq hr N < (hillFreeBandFrequency N)^2 := by
  obtain ⟨p, _, hu⟩ := hillRealLabels_high_pair q hq hr N hN hcut
  obtain ⟨s, hl, _⟩ := hillRealLabels_high_pair q hq hr (N+1) (by omega) (by push_cast; linarith)
  rw [show 2*(N+1)-1 = 2*N+1 by omega] at hl
  obtain ⟨hpL, hpU⟩ := abs_le.mp (p.localization q hq N (by omega) hcut).2
  have hsU := (abs_le.mp (s.localization q hq (N+1) (by omega) (by push_cast; linarith)).1).2
  have hη := (hillRealGapCollar_le_bands q hq hr N).2
  rw [hu, hl] at hη
  have hends := (hillRealGapContour_geometry q hq hr N (by omega)).2.2.2.1
  rw [hu] at hends
  have he : (hillFreeBandFrequency N)^2 - freeHillValue N = Real.pi^2*((N : ℝ)+1/4) := by
    simp only [hillFreeBandFrequency, freeHillValue, Int.cast_natCast]
    ring
  have hd : freeHillValue ((N+1 : ℕ) : ℤ) - freeHillValue N = Real.pi^2*(2*(N : ℝ)+1) := by
    dsimp only [freeHillValue]
    push_cast
    ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hπ : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hb : 0 ≤ (N : ℝ)/4-1/8 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hπ.le hb
  dsimp only [hillRealGapOuterRadius]
  nlinarith

theorem hillRealGapOuter_enclosed_free (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hground : -(hillFreeBandFrequency N)^2 < hillLowestEnergy q hq hr)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    closedBall (hillRealGapCenter q hq hr n : ℂ) (hillRealGapOuterRadius q hq hr n) ⊆
      ball (0 : ℂ) ((hillFreeBandFrequency N)^2) := by
  let E := (hillFreeBandFrequency N)^2
  have hleft : -E < hillRealGapCenter q hq hr n - hillRealGapOuterRadius q hq hr n :=
    hground.trans ((monotone_hillRealLabels q hq hr (Nat.zero_le (2*n-2))).trans_lt
      (hillRealGapOuter_endpoints q hq hr n hn).1)
  have hright : hillRealGapCenter q hq hr n + hillRealGapOuterRadius q hq hr n < E := by
    rcases lt_or_eq_of_le hnN with hlt | rfl
    · exact ((hillRealGapOuter_endpoints q hq hr n hn).2.trans_le
        (monotone_hillRealLabels q hq hr (show 2*n+1 ≤ 2*N by omega))).trans
          (hillFreeBandFrequency_sq_mem_band q hq hr N hN hcut).1
    · exact hillRealGapOuter_last_lt_free_energy q hq hr n hN hcut
  have hc : (-E+E)/2 = 0 := by ring
  have hR : (E-(-E))/2 = E := by ring
  simpa only [hc, hR, ofReal_zero] using
    real_closedBall_subset_diameter_ball _ _ (-E) E hleft hright

end NLS.KdV
