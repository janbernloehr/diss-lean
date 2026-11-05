import NLS.SequenceSpaces.RealWeightedNatPair
import NLS.KdV.HillOriginalRealBirkhoffCoordinates

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.KdV

/-- Exact base normalization for the paper's real positive-index target. -/
def hillBirkhoffBaseWeight (k : ℕ) : ℝ := Real.sqrt (2*Real.pi*(k+1 : ℕ))
theorem hillBirkhoffBaseWeight_pos (k : ℕ) : 0 < hillBirkhoffBaseWeight k := by
  dsimp only [hillBirkhoffBaseWeight]
  positivity

/-- The paper's h_*^0, as actual raw real coordinate pairs with their
weighted Hilbert norm. Index k represents the positive physical index k+1. -/
abbrev HillBirkhoffSpace := RealWeightedNatPair hillBirkhoffBaseWeight hillBirkhoffBaseWeight_pos

def hillBirkhoffSobolevWeight (m k : ℕ) : ℝ := Real.sqrt ((2*Real.pi*(k+1 : ℕ))^(2*m+1))
theorem hillBirkhoffSobolevWeight_pos (m k : ℕ) : 0 < hillBirkhoffSobolevWeight m k := by
  dsimp only [hillBirkhoffSobolevWeight]
  positivity

/-- The paper's h_*^m, with EXACT homogeneous target powers 2m+1. -/
abbrev HillBirkhoffSobolevSpace (m : ℕ) := RealWeightedNatPair
  (hillBirkhoffSobolevWeight m) (hillBirkhoffSobolevWeight_pos m)

def hillBirkhoffWeightedWeight (w : SpectralWeight) (k : ℕ) : ℝ :=
  w (2*((k+1 : ℕ) : ℤ))*hillBirkhoffBaseWeight k

theorem hillBirkhoffWeightedWeight_pos (w : SpectralWeight) (k : ℕ) :
    0 < hillBirkhoffWeightedWeight w k := mul_pos (w.positive _) (hillBirkhoffBaseWeight_pos k)

/-- The paper's h_*^w, with raw real coordinates and the exact w_(2n). -/
abbrev HillBirkhoffWeightedSpace (w : SpectralWeight) := RealWeightedNatPair
  (hillBirkhoffWeightedWeight w) (hillBirkhoffWeightedWeight_pos w)

theorem norm_HillBirkhoffSpace_sq (z : HillBirkhoffSpace) :
    ‖z‖^2 = ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))*((z.val k).1^2+(z.val k).2^2) := by
  rw [RealWeightedNatPair.norm_sq_eq_tsum]
  apply tsum_congr
  intro k
  rw [hillBirkhoffBaseWeight,Real.sq_sqrt (by positivity)]

theorem norm_HillBirkhoffSobolevSpace_sq (m : ℕ) (z : HillBirkhoffSobolevSpace m) :
    ‖z‖^2 = ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*m+1)*((z.val k).1^2+(z.val k).2^2) := by
  rw [RealWeightedNatPair.norm_sq_eq_tsum]
  apply tsum_congr
  intro k
  rw [hillBirkhoffSobolevWeight,Real.sq_sqrt (by positivity)]

theorem norm_HillBirkhoffWeightedSpace_sq (w : SpectralWeight) (z : HillBirkhoffWeightedSpace w) :
    ‖z‖^2 = ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))*(w (2*((k+1 : ℕ) : ℤ)))^2*
      ((z.val k).1^2+(z.val k).2^2) := by
  rw [RealWeightedNatPair.norm_sq_eq_tsum]
  apply tsum_congr
  intro k
  rw [hillBirkhoffWeightedWeight,mul_pow,hillBirkhoffBaseWeight,Real.sq_sqrt (by positivity)]
  ring

end NLS.KdV
