import NLS.KdV.ClassicalHillFlow

/-! The original scalar Dirichlet characteristic is the terminal position
of the actual Hill IVP with initial position zero and derivative one. -/
noncomputable section
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

/-- The exact position/derivative normalized Dirichlet characteristic. -/
def classicalHillDirichlet (q : Curve ℂ) (lambda : ℂ) : ℂ :=
  (classicalHillFlow q lambda (0,1) 1).1

/-- Its first-order frequency realization has a fixed initial vector,
including at zero frequency. -/
theorem classicalHillDirichlet_sq (q : Curve ℂ) (z : ℂ) :
    classicalHillDirichlet q (z^2) =
      (classicalSolution (constantUpperPotential q) z (0,I) 1).1 := by
  have h := classicalHillFlow_eq_constantUpper q z (0,1)
    ⟨1,by constructor <;> norm_num⟩
  simpa only [classicalHillDirichlet,constantUpperStateMap_apply,constantUpperInitialVector,
    mul_zero,mul_one,sub_zero] using congrArg Prod.fst h

/-- Adding a constant potential translates the actual Dirichlet energy. -/
theorem classicalHillDirichlet_add_const (q : Curve ℂ) (c lambda : ℂ) :
    classicalHillDirichlet (q+ContinuousMap.const _ c) lambda = classicalHillDirichlet q (lambda-c) := by
  have he : classicalHillCoefficientCurve (q+ContinuousMap.const _ c) lambda =
      classicalHillCoefficientCurve q (lambda-c) := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    change (v.2,((q t+c)-lambda)*v.1) = (v.2,(q t-(lambda-c))*v.1)
    congr 1
    ring
  change (solution (classicalHillCoefficientCurve (q+ContinuousMap.const _ c) lambda) (0,1) 1).1 = _
  rw [he]
  rfl

/-- The free characteristic at zero energy is one, so zero is not an
artificial Dirichlet root introduced by the frequency coordinate. -/
theorem classicalHillDirichlet_free_zero : classicalHillDirichlet 0 0 = 1 := by
  have h := solution_unique (classicalHillCoefficientCurve 0 0) ((0:ℂ),1)
    (fun x : ℝ => ((x:ℂ),1)) (by fun_prop) (by simp) (by
      intro t _
      convert! (Complex.ofRealCLM.hasDerivAt.prodMk (hasDerivAt_const (t:ℝ) (1:ℂ))) using 1
      simp only [classicalHillCoefficientCurve,ContinuousMap.coe_mk,
        ContinuousLinearMap.coe_restrictScalars',classicalHillCoefficient_apply,
        ContinuousMap.zero_apply,sub_self,zero_mul,Complex.ofRealCLM_apply,ofReal_one])
    (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simpa only [classicalHillDirichlet,classicalHillFlow,ofReal_one] using (congrArg Prod.fst h).symm

end NLS.KdV
