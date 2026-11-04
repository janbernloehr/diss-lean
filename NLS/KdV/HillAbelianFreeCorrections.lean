import NLS.KdV.HillNativeFreeSpectralData
import NLS.KdV.HillAbelianPhysicalPhaseFormula

/-! The ACTUAL physical sheet makes all diagonal and individual off-index
corrections vanish at the free source. The literal infinite correction
therefore vanishes too, with both full phase multipliers exactly one. -/
noncomputable section
open Set Metric Complex
open scoped Classical
namespace NLS.KdV
namespace HillProductEquationPatch

theorem physicalDirichletRootCoefficient_zero (P : HillProductEquationPatch) (n : ℕ+) :
    P.physicalDirichletRootCoefficient n 0 = 0 := by
  simp only [physicalDirichletRootCoefficient,hillHminusDirichletSheet_zero,zero_div]

theorem physicalOnIndexAbelianCorrection_zero (P : HillProductEquationPatch) (n : ℕ+) :
    P.physicalOnIndexAbelianCorrection n 0 = 0 :=
  P.physicalOnIndexAbelianCorrection_zero_of_sheet_zero n 0 (hillHminusDirichletSheet_zero n)

theorem physicalOffIndexAbelianValue_zero (P : HillProductEquationPatch) (n m : ℕ+) :
    P.physicalOffIndexAbelianValue n m 0 = 0 := by
  simp only [physicalOffIndexAbelianValue,P.physicalDirichletRootCoefficient_zero,zero_mul]

theorem physicalOffIndexAbelianTerm_zero (P : HillProductEquationPatch) (n m : ℕ+) :
    P.physicalOffIndexAbelianTerm n 0 m = 0 := by
  simp only [physicalOffIndexAbelianTerm,P.physicalOffIndexAbelianValue_zero,ite_self]

theorem physicalOffIndexAbelianCorrection_zero (P : HillProductEquationPatch) (n : ℕ+) :
    P.physicalOffIndexAbelianCorrection n 0 = 0 := by
  simp only [physicalOffIndexAbelianCorrection,P.physicalOffIndexAbelianTerm_zero,tsum_zero]

end HillProductEquationPatch

theorem hillHminusOffIndexAbelianCorrection_zero (n : ℕ+) :
    hillHminusOffIndexAbelianCorrection n 0 = 0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch 0 hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_offIndex_correction_patch_ball P 0 hq hr
  rw [(heq n 0 (mem_ball_self hrpos)).2.2,P.physicalOffIndexAbelianCorrection_zero]

theorem hillHminusOffIndex_phase_exponentials_zero (n : ℕ+) :
    Complex.exp (I*hillHminusOffIndexAbelianCorrection n 0) = 1 ∧
      Complex.exp (-I*hillHminusOffIndexAbelianCorrection n 0) = 1 := by
  simp only [hillHminusOffIndexAbelianCorrection_zero,mul_zero,Complex.exp_zero,and_self]

end NLS.KdV
