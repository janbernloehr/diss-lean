import NLS.KdV.ClassicalHillTraceGradient

/-! The actual discriminant gradient solves the squared-eigenfunction
third-order equation. The potential need only have the stated first
derivative at the point; energies and potentials are allowed to be complex. -/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.KdV

def classicalHillTraceGradientPrime (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ :=
  (2*classicalHillS q μ 1)*(classicalHillC q μ x*classicalHillCPrime q μ x)+
    (classicalHillSPrime q μ 1-classicalHillC q μ 1)*
      (classicalHillCPrime q μ x*classicalHillS q μ x+classicalHillC q μ x*classicalHillSPrime q μ x)-
    (2*classicalHillCPrime q μ 1)*(classicalHillS q μ x*classicalHillSPrime q μ x)

def classicalHillTraceGradientKinetic (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ :=
  classicalHillS q μ 1*(classicalHillCPrime q μ x)^2+
    (classicalHillSPrime q μ 1-classicalHillC q μ 1)*(classicalHillCPrime q μ x*classicalHillSPrime q μ x)-
    classicalHillCPrime q μ 1*(classicalHillSPrime q μ x)^2

def classicalHillTraceGradientSecond (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ :=
  2*((extend q x-μ)*classicalHillTraceGradient q μ x)+2*classicalHillTraceGradientKinetic q μ x

theorem continuous_classicalHillTraceGradientPrime (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillTraceGradientPrime q μ) := by
  have hC := continuous_classicalHillC q μ
  have hCp := continuous_classicalHillCPrime q μ
  have hS := continuous_classicalHillS q μ
  have hSp := continuous_classicalHillSPrime q μ
  change Continuous (fun x : ℝ => (2*classicalHillS q μ 1)*(classicalHillC q μ x*classicalHillCPrime q μ x)+(classicalHillSPrime q μ 1-classicalHillC q μ 1)*(classicalHillCPrime q μ x*classicalHillS q μ x+classicalHillC q μ x*classicalHillSPrime q μ x)-(2*classicalHillCPrime q μ 1)*(classicalHillS q μ x*classicalHillSPrime q μ x))
  fun_prop (disch := assumption)

theorem continuous_classicalHillTraceGradientKinetic (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillTraceGradientKinetic q μ) := by
  have hCp := continuous_classicalHillCPrime q μ
  have hSp := continuous_classicalHillSPrime q μ
  change Continuous (fun x : ℝ => classicalHillS q μ 1*(classicalHillCPrime q μ x)^2+(classicalHillSPrime q μ 1-classicalHillC q μ 1)*(classicalHillCPrime q μ x*classicalHillSPrime q μ x)-classicalHillCPrime q μ 1*(classicalHillSPrime q μ x)^2)
  fun_prop (disch := assumption)

theorem continuous_classicalHillTraceGradientSecond (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillTraceGradientSecond q μ) :=
  (continuous_const.mul (((continuous_extend q).sub continuous_const).mul
    (continuous_classicalHillTraceGradient q μ))).add
      (continuous_const.mul (continuous_classicalHillTraceGradientKinetic q μ))

theorem hasDerivAt_classicalHillTraceGradient (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillTraceGradient q μ) (classicalHillTraceGradientPrime q μ t) t := by
  have hC := hasDerivAt_classicalHillC q μ t
  have hS := hasDerivAt_classicalHillS q μ t
  have hd := (((hC.pow 2).const_mul (classicalHillS q μ 1)).add
    ((hC.mul hS).const_mul (classicalHillSPrime q μ 1-classicalHillC q μ 1))).sub
      ((hS.pow 2).const_mul (classicalHillCPrime q μ 1))
  convert hd using 1 <;> first
  | rfl
  | (dsimp only [classicalHillTraceGradient,classicalHillTraceGradientPrime,classicalHillTraceGradientKinetic,
      Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]; ring)

theorem hasDerivAt_classicalHillTraceGradientPrime (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillTraceGradientPrime q μ) (classicalHillTraceGradientSecond q μ t) t := by
  have hC := hasDerivAt_classicalHillC q μ t
  have hCp := hasDerivAt_classicalHillCPrime q μ t
  have hS := hasDerivAt_classicalHillS q μ t
  have hSp := hasDerivAt_classicalHillSPrime q μ t
  have hd := (((hC.mul hCp).const_mul (2*classicalHillS q μ 1)).add
    (((hCp.mul hS).add (hC.mul hSp)).const_mul (classicalHillSPrime q μ 1-classicalHillC q μ 1))).sub
      ((hS.mul hSp).const_mul (2*classicalHillCPrime q μ 1))
  convert hd using 1 <;> first
  | rfl
  | (simp only [classicalHillTraceGradientSecond,classicalHillTraceGradient,classicalHillTraceGradientKinetic,
      extend_coe]; ring)

theorem hasDerivAt_classicalHillTraceGradientKinetic (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillTraceGradientKinetic q μ)
      ((q t-μ)*classicalHillTraceGradientPrime q μ t) t := by
  have hCp := hasDerivAt_classicalHillCPrime q μ t
  have hSp := hasDerivAt_classicalHillSPrime q μ t
  have hd := (((hCp.pow 2).const_mul (classicalHillS q μ 1)).add
    ((hCp.mul hSp).const_mul (classicalHillSPrime q μ 1-classicalHillC q μ 1))).sub
      ((hSp.pow 2).const_mul (classicalHillCPrime q μ 1))
  convert hd using 1 <;> first
  | rfl
  | (dsimp only [classicalHillTraceGradient,classicalHillTraceGradientPrime,classicalHillTraceGradientKinetic,
      Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]; ring)

theorem hasDerivAt_classicalHillTraceGradientSecond (q : Curve ℂ) (μ qdot : ℂ)
    (t : Icc (0:ℝ) 1) (hq : HasDerivAt (extend q) qdot t) :
    HasDerivAt (classicalHillTraceGradientSecond q μ)
      (2*qdot*classicalHillTraceGradient q μ t+4*(q t-μ)*classicalHillTraceGradientPrime q μ t) t := by
  have hG := hasDerivAt_classicalHillTraceGradient q μ t
  have hK := hasDerivAt_classicalHillTraceGradientKinetic q μ t
  have hd := (((hq.sub_const μ).mul hG).const_mul 2).add (hK.const_mul 2)
  convert hd using 1 <;> first
  | rfl
  | (rw [extend_coe]; ring)

end NLS.KdV
