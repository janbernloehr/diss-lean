import NLS.SequenceSpaces.FourierRealZeroDecomposition
import NLS.ComplexAnalysis.ContractiveComplexification

/-! The physical Fourier real form has contractive real/imaginary projections
inside its ORIGINAL complex zero-mode weighted space, at every Banach exponent. -/
noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_fourierRealZeroProjection_le (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) : ‖fourierRealZeroProjection w hw a‖≤‖a‖ := by
  have hJ : ‖zeroModeConjugation w hw a‖=‖a‖ := norm_conjugateReflection w hw a.val
  change ‖(1/2:ℝ) • (a+zeroModeConjugation w hw a)‖≤‖a‖
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    (1/2:ℝ)*‖a+zeroModeConjugation w hw a‖ ≤ (1/2:ℝ)*(‖a‖+‖zeroModeConjugation w hw a‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖a‖ := by rw [hJ]; ring

def fourierRealZeroImagProjection (w : Weight) (hw : ∀ k, w (-k)=w k) :
    zeroModeSubmodule w p →L[ℝ] fourierRealZeroSubmodule w p :=
  (fourierRealZeroProjection w hw).comp
    (((-I) • ContinuousLinearMap.id ℂ (zeroModeSubmodule w p)).restrictScalars ℝ)

theorem fourierRealZeroImagProjection_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) :
    fourierRealZeroImagProjection w hw a=fourierRealZeroProjection w hw ((-I) • a) := rfl

def fourierRealContractiveComplexification (w : Weight) (hw : ∀ k, w (-k)=w k) :
    ContractiveComplexification (fourierRealZeroSubmodule w p) (zeroModeSubmodule w p) where
  inclusion := (fourierRealZeroSubmodule w p).subtypeL
  re := fourierRealZeroProjection w hw
  im := fourierRealZeroImagProjection w hw
  re_inclusion := fourierRealZeroProjection_inclusion w hw
  im_inclusion a := by
    change fourierRealZeroProjection w hw ((-I) • a.val)=0
    rw [neg_smul,map_neg,fourierRealZeroProjection_I_smul,neg_zero]
  re_I a := by
    change fourierRealZeroProjection w hw (I • a)= -fourierRealZeroProjection w hw ((-I) • a)
    rw [neg_smul,map_neg,neg_neg]
  im_I a := by
    change fourierRealZeroProjection w hw ((-I) • (I • a))=fourierRealZeroProjection w hw a
    simp only [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  norm_re := norm_fourierRealZeroProjection_le w hw
  norm_im a := by
    change ‖fourierRealZeroProjection w hw ((-I) • a)‖≤‖a‖
    calc
      _ ≤ ‖(-I) • a‖ := norm_fourierRealZeroProjection_le w hw _
      _ = ‖a‖ := by rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
  decomposition := fourierRealZeroProjection_decomposition w hw

end NLS.WeightedCoeff
