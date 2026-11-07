import NLS.KdV.ClassicalHillTraceGradientJets

/-! The actual trace gradient and its first two jets close at the physical
unit endpoints. Only the potential's endpoint equality is needed for the
second jet; all monodromy identities use its PROVED determinant one. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

theorem classicalHillTraceGradient_initial (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradient q μ 0=classicalHillS q μ 1 := by
  obtain ⟨hC,_,hS,_⟩ := classicalHillFundamentalColumns_initial q μ
  simp [classicalHillTraceGradient,hC,hS]

theorem classicalHillTraceGradient_terminal (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradient q μ 1=classicalHillS q μ 1 := by
  have hdet := classicalHillFundamentalColumns_det q μ ⟨1,by constructor <;> norm_num⟩
  dsimp only [classicalHillTraceGradient]
  linear_combination classicalHillS q μ 1*hdet

theorem classicalHillTraceGradientPrime_initial (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradientPrime q μ 0=classicalHillSPrime q μ 1-classicalHillC q μ 1 := by
  obtain ⟨hC,hCp,hS,hSp⟩ := classicalHillFundamentalColumns_initial q μ
  simp [classicalHillTraceGradientPrime,hC,hCp,hS,hSp]

theorem classicalHillTraceGradientPrime_terminal (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradientPrime q μ 1=classicalHillSPrime q μ 1-classicalHillC q μ 1 := by
  have hdet := classicalHillFundamentalColumns_det q μ ⟨1,by constructor <;> norm_num⟩
  dsimp only [classicalHillTraceGradientPrime]
  linear_combination (classicalHillSPrime q μ 1-classicalHillC q μ 1)*hdet

theorem classicalHillTraceGradientKinetic_initial (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradientKinetic q μ 0= -classicalHillCPrime q μ 1 := by
  obtain ⟨_,hCp,_,hSp⟩ := classicalHillFundamentalColumns_initial q μ
  simp [classicalHillTraceGradientKinetic,hCp,hSp]

theorem classicalHillTraceGradientKinetic_terminal (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradientKinetic q μ 1= -classicalHillCPrime q μ 1 := by
  have hdet := classicalHillFundamentalColumns_det q μ ⟨1,by constructor <;> norm_num⟩
  dsimp only [classicalHillTraceGradientKinetic]
  linear_combination -classicalHillCPrime q μ 1*hdet

theorem classicalHillTraceGradient_boundary (q : Curve ℂ) (μ : ℂ) :
    classicalHillTraceGradient q μ 1=classicalHillTraceGradient q μ 0 ∧
      classicalHillTraceGradientPrime q μ 1=classicalHillTraceGradientPrime q μ 0 := by
  rw [classicalHillTraceGradient_initial,classicalHillTraceGradient_terminal,
    classicalHillTraceGradientPrime_initial,classicalHillTraceGradientPrime_terminal]
  exact ⟨rfl,rfl⟩

theorem classicalHillTraceGradientSecond_boundary (q : Curve ℂ) (μ : ℂ)
    (hq : extend q 1=extend q 0) :
    classicalHillTraceGradientSecond q μ 1=classicalHillTraceGradientSecond q μ 0 := by
  rw [classicalHillTraceGradientSecond,classicalHillTraceGradientSecond,
    classicalHillTraceGradient_terminal,classicalHillTraceGradient_initial,
    classicalHillTraceGradientKinetic_terminal,classicalHillTraceGradientKinetic_initial,hq]

end NLS.KdV
