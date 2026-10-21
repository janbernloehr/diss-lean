import NLS.Fourier.PrintedChirpCoefficients

/-! # Positive decreasing amplitude of the printed A.5 series -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.Fourier

/-- The literal logarithmic amplitude, before the prescribed cutoff at two. -/
def printedChirpAmplitude (x : ℝ) : ℝ := 1/(Real.sqrt x*(Real.log x)^2)

theorem printedChirpAmplitude_nonneg (x : ℝ) : 0 ≤ printedChirpAmplitude x := by
  unfold printedChirpAmplitude
  positivity

theorem printedChirpAmplitude_pos (x : ℝ) (hx : 2 ≤ x) : 0 < printedChirpAmplitude x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  exact div_pos zero_lt_one (mul_pos (Real.sqrt_pos.2 hx0) (sq_pos_of_pos (Real.log_pos hx1)))

/-- The amplitude decreases throughout the range used in the printed series. -/
theorem antitoneOn_printedChirpAmplitude : AntitoneOn printedChirpAmplitude (Ici 2) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by have : 2 ≤ x := hx; linarith
  have hx1 : 1 < x := by have : 2 ≤ x := hx; linarith
  apply one_div_le_one_div_of_le
    (mul_pos (Real.sqrt_pos.2 hx0) (sq_pos_of_pos (Real.log_pos hx1)))
  gcongr
  exact Real.log_nonneg hx1.le

end NLS.Fourier
