import NLS.ComplexAnalysis.CartesianPlaneRotation

/-! # Common complex scalings commute with physical Cartesian rotations -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem cartesianPlaneRotation_smul (c : ℂ) (t : ℝ) (z : ℂ × ℂ) :
    cartesianPlaneRotation t (c • z) = c • cartesianPlaneRotation t z := by
  apply Prod.ext <;> simp only [cartesianPlaneRotation,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

end NLS.ComplexAnalysis
