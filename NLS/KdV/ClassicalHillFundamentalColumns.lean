import NLS.KdV.ClassicalHillWronskian

/-! The four ACTUAL scalar fundamental entries with their original
initial values and spatial derivatives, at every complex energy. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

def classicalHillC (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ := (classicalHillFlow q μ (1,0) x).1
def classicalHillCPrime (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ := (classicalHillFlow q μ (1,0) x).2
def classicalHillS (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ := (classicalHillFlow q μ (0,1) x).1
def classicalHillSPrime (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ := (classicalHillFlow q μ (0,1) x).2

theorem continuous_classicalHillC (q : Curve ℂ) (μ : ℂ) : Continuous (classicalHillC q μ) :=
  (continuous_classicalHillFlow q μ (1,0)).fst
theorem continuous_classicalHillCPrime (q : Curve ℂ) (μ : ℂ) : Continuous (classicalHillCPrime q μ) :=
  (continuous_classicalHillFlow q μ (1,0)).snd
theorem continuous_classicalHillS (q : Curve ℂ) (μ : ℂ) : Continuous (classicalHillS q μ) :=
  (continuous_classicalHillFlow q μ (0,1)).fst
theorem continuous_classicalHillSPrime (q : Curve ℂ) (μ : ℂ) : Continuous (classicalHillSPrime q μ) :=
  (continuous_classicalHillFlow q μ (0,1)).snd

theorem classicalHillFundamentalColumns_initial (q : Curve ℂ) (μ : ℂ) :
    classicalHillC q μ 0=1 ∧ classicalHillCPrime q μ 0=0 ∧
      classicalHillS q μ 0=0 ∧ classicalHillSPrime q μ 0=1 := by
  simp [classicalHillC,classicalHillCPrime,classicalHillS,classicalHillSPrime,classicalHillFlow_zero]

theorem hasDerivAt_classicalHillC (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillC q μ) (classicalHillCPrime q μ t) t := by
  change HasDerivAt (fun x => (classicalHillFlow q μ (1,0) x).1) (classicalHillFlow q μ (1,0) t).2 t
  simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q μ (1,0) t).fst

theorem hasDerivAt_classicalHillCPrime (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillCPrime q μ) ((q t-μ)*classicalHillC q μ t) t := by
  change HasDerivAt (fun x => (classicalHillFlow q μ (1,0) x).2) ((q t-μ)*(classicalHillFlow q μ (1,0) t).1) t
  simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q μ (1,0) t).snd

theorem hasDerivAt_classicalHillS (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillS q μ) (classicalHillSPrime q μ t) t := by
  change HasDerivAt (fun x => (classicalHillFlow q μ (0,1) x).1) (classicalHillFlow q μ (0,1) t).2 t
  simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q μ (0,1) t).fst

theorem hasDerivAt_classicalHillSPrime (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillSPrime q μ) ((q t-μ)*classicalHillS q μ t) t := by
  change HasDerivAt (fun x => (classicalHillFlow q μ (0,1) x).2) ((q t-μ)*(classicalHillFlow q μ (0,1) t).1) t
  simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q μ (0,1) t).snd

theorem classicalHillFundamentalColumns_det (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    classicalHillC q μ t*classicalHillSPrime q μ t-classicalHillCPrime q μ t*classicalHillS q μ t=1 :=
  classicalHillFundamental_wronskian q μ t

end NLS.KdV
