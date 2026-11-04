import NLS.KdV.HillL2GroundSquare

/-! # Finite real band coverage between intrinsic spectral labels

Avoiding the first N closed gaps between the ground energy and the
next band endpoint puts a real energy in one of those open bands.
The proof needs only the checked ordering and neighboring-band separation.
-/

noncomputable section
open Set Complex
namespace NLS.KdV

theorem hillRealLabels_finite_band_cover
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (x : ℝ)
    (hx0 : hillLowestEnergy q hq hr < x)
    (hxN : x < hillRealLabels q hq hr (2 * N + 1))
    (hgap : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      x ∉ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    ∃ k : ℕ, k ≤ N ∧ x ∈ Ioo (hillRealLabels q hq hr (2 * k)) (hillRealLabels q hq hr (2 * k + 1)) := by
  induction N with
  | zero => exact ⟨0, le_rfl, hx0, hxN⟩
  | succ N ih =>
      by_cases hx : x < hillRealLabels q hq hr (2 * N + 1)
      · obtain ⟨k, hk, hmem⟩ := ih hx (fun n hn hN => hgap n hn (by omega))
        exact ⟨k, by omega, hmem⟩
      · have hleft : hillRealLabels q hq hr (2 * (N + 1) - 1) ≤ x := by
          simpa only [show 2 * (N + 1) - 1 = 2 * N + 1 by omega] using not_lt.mp hx
        have hright : hillRealLabels q hq hr (2 * (N + 1)) < x :=
          lt_of_not_ge (fun h => hgap (N + 1) (by omega) le_rfl ⟨hleft, h⟩)
        exact ⟨N + 1, le_rfl, hright, hxN⟩

end NLS.KdV
