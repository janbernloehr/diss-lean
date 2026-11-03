import NLS.KdV.HillL2RealCutDifferential
import NLS.ComplexAnalysis.ContinuousIntervalBranch

/-! # The actual indexed phase throughout every open Hill band

The globally normalized endpoint values and continuity fix the full band
phase. An interior point cannot have either endpoint phase, since its
trace would then be a characteristic endpoint value.
-/

noncomputable section
open Set Complex
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hillL2UpperBoundaryPrimitive_band_phase
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n)) (hillRealLabels q hq hr (2*n+1))) :
    -(hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im ∈
      Ioo ((n : ℝ) * Real.pi) (((n : ℝ)+1) * Real.pi) := by
  let B := hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q)
  let a := hillRealLabels q hq hr (2*n)
  let b := hillRealLabels q hq hr (2*n+1)
  let θ : ℝ → ℝ := fun y => -(B y).im
  have hB : Continuous B := continuous_hillL2UpperBoundaryPrimitive q hq hr
  have haB : B a = -I * (n : ℂ) * Real.pi := by
    simpa only [B, a, show (2*n+1)/2 = n by omega] using
      hillL2UpperBoundaryPrimitive_label_indexed q hq hr (2*n)
  have hbB : B b = -I * ((n+1 : ℕ) : ℂ) * Real.pi := by
    simpa only [B, b, show (2*n+1+1)/2 = n+1 by omega] using
      hillL2UpperBoundaryPrimitive_label_indexed q hq hr (2*n+1)
  have htrace (y : ℝ) : 2 * cosh (B y) = hillL2Discriminant (SpectralWeight.one.toCoeff q) y := by
    simpa only [hillL2RealCutPrimitive, ofReal_im, if_true, ofReal_re, B] using
      hillL2RealCutPrimitive_trace q hq hr (y : ℂ)
  have hne (y : ℝ) (hy : y ∈ Ioo a b) (j : ℕ) :
      B y ≠ B (hillRealLabels q hq hr j) := by
    intro he
    have hD : hillL2Discriminant (SpectralWeight.one.toCoeff q) y =
        hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr j) := by
      rw [← htrace y, he, htrace]
    have hzero := (hillRealLabels_spec q hq hr).root j
    apply hillL2Radicand_ne_zero_between_labels q hq hr (2*n) y hy
    simpa only [hillL2Radicand, hD] using hzero
  apply mem_Ioo_of_continuous_avoiding_endpoint_levels θ a b _ _
    ((continuous_im.comp hB).neg.continuousOn) _ _ (by linarith [Real.pi_pos]) _ x hx
  · simp [θ, haB]
  · simp [θ, hbB, Nat.cast_add, Nat.cast_one]
  · intro y hy
    have hre : (B y).re = 0 := hillL2UpperBoundaryPrimitive_re_eq_zero_band q hq hr n y hy
    constructor
    · intro he
      apply hne y hy (2*n)
      apply Complex.ext
      · change (B y).re = (B a).re
        rw [haB]
        simpa using hre
      · have haθ : θ a = (n : ℝ) * Real.pi := by simp [θ, haB]
        change θ y = (n : ℝ) * Real.pi at he
        dsimp only [θ] at haθ he
        linarith
    · intro he
      apply hne y hy (2*n+1)
      apply Complex.ext
      · change (B y).re = (B b).re
        rw [hbB]
        simpa using hre
      · have hbθ : θ b = ((n : ℝ)+1) * Real.pi := by simp [θ, hbB, Nat.cast_add, Nat.cast_one]
        change θ y = ((n : ℝ)+1) * Real.pi at he
        dsimp only [θ] at hbθ he
        linarith

end NLS.KdV
