import NLS.ZakharovShabat.SourcePsiUniformEquationTube

/-! # Restricting uniform psi equation tubes without changing their equations -/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePsiUniformEquationTube
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {φ : realTypeSourceLocus p}

def restrictRadius (D : SourcePsiUniformEquationTube hp hp1 φ)
    (r : ℝ) (hr : 0 < r) (hrD : r ≤ D.radius) : SourcePsiUniformEquationTube hp hp1 φ where
  equation := D.equation
  radius := r
  normBound := D.normBound
  inverseBound := D.inverseBound
  radius_pos := hr
  normBound_nonneg := D.normBound_nonneg
  inverseBound_nonneg := D.inverseBound_nonneg
  analytic := fun n => (D.analytic n).mono (ball_subset_ball (by linarith))
  norm_le := fun n q hq => D.norm_le n q (ball_subset_ball (by linarith) hq)
  zero := D.zero
  contours := fun n q hq => D.contours n q (ball_subset_ball (by linarith) hq)
  inverse := fun n q hq => D.inverse n q (ball_subset_ball (by linarith) hq)

end NLS.ZakharovShabat.SourcePsiUniformEquationTube
