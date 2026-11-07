import NLS.KdV.ClassicalHillFundamentalColumns

/-! Quadratic kernels of the ACTUAL normalized Hill fundamental
columns. Their closed first-order jet system needs only a continuous
complex potential and is uniform in all three quadratic coefficients. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

def classicalHillQuadraticKernel (q : Curve ℂ) (μ α β γ : ℂ) (x : ℝ) : ℂ :=
  α*(classicalHillC q μ x)^2+β*(classicalHillC q μ x*classicalHillS q μ x)+γ*(classicalHillS q μ x)^2

def classicalHillQuadraticKernelPrime (q : Curve ℂ) (μ α β γ : ℂ) (x : ℝ) : ℂ :=
  2*α*(classicalHillC q μ x*classicalHillCPrime q μ x)+
    β*(classicalHillCPrime q μ x*classicalHillS q μ x+classicalHillC q μ x*classicalHillSPrime q μ x)+
      2*γ*(classicalHillS q μ x*classicalHillSPrime q μ x)

def classicalHillQuadraticKernelKinetic (q : Curve ℂ) (μ α β γ : ℂ) (x : ℝ) : ℂ :=
  α*(classicalHillCPrime q μ x)^2+β*(classicalHillCPrime q μ x*classicalHillSPrime q μ x)+
    γ*(classicalHillSPrime q μ x)^2

theorem continuous_classicalHillQuadraticKernel (q : Curve ℂ) (μ α β γ : ℂ) :
    Continuous (classicalHillQuadraticKernel q μ α β γ) :=
  ((continuous_const.mul ((continuous_classicalHillC q μ).pow 2)).add
    (continuous_const.mul ((continuous_classicalHillC q μ).mul (continuous_classicalHillS q μ)))).add
      (continuous_const.mul ((continuous_classicalHillS q μ).pow 2))

theorem continuous_classicalHillQuadraticKernelPrime (q : Curve ℂ) (μ α β γ : ℂ) :
    Continuous (classicalHillQuadraticKernelPrime q μ α β γ) := by
  have hC := continuous_classicalHillC q μ
  have hCp := continuous_classicalHillCPrime q μ
  have hS := continuous_classicalHillS q μ
  have hSp := continuous_classicalHillSPrime q μ
  change Continuous (fun x : ℝ => 2*α*(classicalHillC q μ x*classicalHillCPrime q μ x)+
    β*(classicalHillCPrime q μ x*classicalHillS q μ x+classicalHillC q μ x*classicalHillSPrime q μ x)+
      2*γ*(classicalHillS q μ x*classicalHillSPrime q μ x))
  fun_prop

theorem continuous_classicalHillQuadraticKernelKinetic (q : Curve ℂ) (μ α β γ : ℂ) :
    Continuous (classicalHillQuadraticKernelKinetic q μ α β γ) :=
  ((continuous_const.mul ((continuous_classicalHillCPrime q μ).pow 2)).add
    (continuous_const.mul ((continuous_classicalHillCPrime q μ).mul (continuous_classicalHillSPrime q μ)))).add
      (continuous_const.mul ((continuous_classicalHillSPrime q μ).pow 2))

theorem hasDerivAt_classicalHillQuadraticKernel (q : Curve ℂ) (μ α β γ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillQuadraticKernel q μ α β γ) (classicalHillQuadraticKernelPrime q μ α β γ t) t := by
  have hC := hasDerivAt_classicalHillC q μ t
  have hS := hasDerivAt_classicalHillS q μ t
  have hd := (((hC.pow 2).const_mul α).add ((hC.mul hS).const_mul β)).add ((hS.pow 2).const_mul γ)
  convert hd using 1 <;> first
  | rfl
  | (dsimp only [classicalHillQuadraticKernel,classicalHillQuadraticKernelPrime,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]; ring)

theorem hasDerivAt_classicalHillQuadraticKernelPrime (q : Curve ℂ) (μ α β γ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillQuadraticKernelPrime q μ α β γ)
      (2*(q t-μ)*classicalHillQuadraticKernel q μ α β γ t+2*classicalHillQuadraticKernelKinetic q μ α β γ t) t := by
  have hC := hasDerivAt_classicalHillC q μ t
  have hCp := hasDerivAt_classicalHillCPrime q μ t
  have hS := hasDerivAt_classicalHillS q μ t
  have hSp := hasDerivAt_classicalHillSPrime q μ t
  have hd := (((hC.mul hCp).const_mul (2*α)).add (((hCp.mul hS).add (hC.mul hSp)).const_mul β)).add
    ((hS.mul hSp).const_mul (2*γ))
  convert hd using 1 <;> first
  | rfl
  | (dsimp only [classicalHillQuadraticKernel,classicalHillQuadraticKernelKinetic]; ring)

theorem hasDerivAt_classicalHillQuadraticKernelKinetic (q : Curve ℂ) (μ α β γ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillQuadraticKernelKinetic q μ α β γ)
      ((q t-μ)*classicalHillQuadraticKernelPrime q μ α β γ t) t := by
  have hCp := hasDerivAt_classicalHillCPrime q μ t
  have hSp := hasDerivAt_classicalHillSPrime q μ t
  have hd := (((hCp.pow 2).const_mul α).add ((hCp.mul hSp).const_mul β)).add ((hSp.pow 2).const_mul γ)
  convert hd using 1 <;> first
  | rfl
  | (dsimp only [classicalHillQuadraticKernelPrime]; ring)

end NLS.KdV
