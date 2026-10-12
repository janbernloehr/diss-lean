import NLS.ZakharovShabat.L2FundamentalAnalytic

/-! # The physical L2 fundamental matrix acts on arbitrary initial data -/
noncomputable section
open Set Complex
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Initial data enter the original L2 solution complex linearly. -/
theorem l2SolutionCurve_linearCombination (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    l2SolutionCurve u z v =
      v.1 • l2SolutionCurve u z (1,0)+v.2 • l2SolutionCurve u z (0,1) := by
  simp only [l2SolutionCurve_eq_l2SolutionOperator]
  rw [← map_smul,← map_smul,← map_add]
  congr 1
  ext t <;> simp [smul_eq_mul]

/-- Multiplication by an initial matrix consists of the actual initial-value solutions. -/
theorem l2FundamentalMatrix_mul_column (u : IntervalPairL2) (z : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) (t : Icc (0 : ℝ) 1) :
    ((l2FundamentalMatrix u z t*A) 0 j,(l2FundamentalMatrix u z t*A) 1 j) =
      l2SolutionCurve u z (A 0 j,A 1 j) t := by
  rw [l2SolutionCurve_linearCombination]
  apply Prod.ext <;>
    simp [l2FundamentalMatrix,Matrix.mul_apply,Fin.sum_univ_two,smul_eq_mul] <;> ring

end NLS.ZakharovShabat
