import NLS.ZakharovShabat.ClassicalForcedParity

/-!
# Repeated zero-initial forced solutions

A bounded operator on continuous curves advances the original `z-L` chain
by one zero-initial forced step. Its powers give normalized classical chain
curves, retaining the actual differential equation and the initial values.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The homogeneous classical solution, as a continuous curve on the unit interval. -/
def classicalSolutionCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  solutionCurve (classicalODECurve Φ z) v

@[simp] theorem classicalSolutionCurve_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) : classicalSolutionCurve Φ z v t = classicalSolution Φ z v t :=
  (solution_coe _ _ t).symm

/-- The homogeneous curve is the inverse Volterra operator applied to constant initial data. -/
theorem classicalSolutionCurve_eq_inverse (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalSolutionCurve Φ z v =
      solutionOperator (classicalCoefficientCurveCLM (z,Φ)) (ContinuousMap.const _ v) := by
  unfold classicalSolutionCurve
  rw [← realCoefficient_classicalCoefficientCurve (z,Φ),solutionCurve_eq_solutionOperator]

/-- The bounded operator which solves one zero-initial original source equation. -/
def classicalChainOperator (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  solutionOperator (classicalCoefficientCurveCLM (z,Φ)) *
    volterra (ContinuousMap.const _ classicalSource)

/-- Integrating the signed source is the constant-coefficient Volterra operator. -/
theorem primitive_classicalSourceCurve (g : Curve (ℂ × ℂ)) :
    primitive (classicalSourceCurve g) = volterra (ContinuousMap.const _ classicalSource) g := by
  apply ContinuousMap.ext
  intro t
  rw [primitive_apply,volterra_apply]
  rfl

/-- Applying the chain operator is exactly the constructed forced solution curve. -/
theorem classicalChainOperator_eq_forced (Φ : Curve (ℂ × ℂ)) (z : ℂ) (g : Curve (ℂ × ℂ)) :
    classicalChainOperator Φ z g =
      forcedSolutionCurve (classicalCoefficientCurveCLM (z,Φ)) (classicalSourceCurve g) 0 := by
  simp only [classicalChainOperator,mul_apply_eq_comp,forcedSolutionCurve,
    show ContinuousMap.const (Icc (0 : ℝ) 1) (0 : ℂ × ℂ) = 0 from rfl,zero_add,
    primitive_classicalSourceCurve]

/-- Pointwise evaluation of the chain operator retains the actual forced solution. -/
theorem classicalChainOperator_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (g : Curve (ℂ × ℂ))
    (t : Icc (0 : ℝ) 1) :
    classicalChainOperator Φ z g t = classicalForcedSolution Φ z g 0 t := by
  rw [classicalChainOperator_eq_forced]
  exact (forcedSolution_coe _ _ _ t).symm

/-- Repeated zero-initial forcing, starting from a homogeneous initial vector. -/
def classicalChainCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  (classicalChainOperator Φ z ^ n) (classicalSolutionCurve Φ z v)

@[simp] theorem classicalChainCurve_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalChainCurve Φ z 0 v = classicalSolutionCurve Φ z v := rfl

/-- Every next curve is obtained by one more application of the same bounded source solver. -/
theorem classicalChainCurve_succ (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) :
    classicalChainCurve Φ z (n+1) v = classicalChainOperator Φ z (classicalChainCurve Φ z n v) := by
  simp only [classicalChainCurve,pow_succ',mul_apply_eq_comp]

/-- A physical representative of each normalized classical chain curve. -/
def classicalChainSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℕ → (ℂ × ℂ) → ℝ → ℂ × ℂ
  | 0,v => classicalSolution Φ z v
  | n+1,v => classicalForcedSolution Φ z (classicalChainCurve Φ z n v) 0

/-- The physical and continuous-curve constructions agree throughout the closed unit interval. -/
theorem classicalChainSolution_coe (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) : classicalChainSolution Φ z n v t = classicalChainCurve Φ z n v t := by
  cases n with
  | zero => exact (classicalSolutionCurve_apply Φ z v t).symm
  | succ n => rw [classicalChainCurve_succ,classicalChainOperator_apply]; rfl

/-- All positive chain levels have zero initial data. -/
@[simp] theorem classicalChainSolution_succ_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) :
    classicalChainSolution Φ z (n+1) v 0 = 0 := classicalForcedSolution_zero _ _ _ _

/-- Every successive chain curve satisfies the actual original inhomogeneous pencil equation. -/
theorem physicalPencil_classicalChainSolution_succ (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    z • classicalChainSolution Φ z (n+1) v t-
      physicalOperator (extend Φ) (classicalChainSolution Φ z (n+1) v) t =
        classicalChainSolution Φ z n v t := by
  rw [classicalChainSolution_coe Φ z n v t]
  exact physicalPencil_classicalForcedSolution Φ z (classicalChainCurve Φ z n v) 0 t

/-- The bounded chain operator controls every coefficient in the supremum norm. -/
theorem norm_classicalChainCurve_le (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) :
    ‖classicalChainCurve Φ z n v‖ ≤ ‖classicalChainOperator Φ z‖^n * ‖classicalSolutionCurve Φ z v‖ :=
  ((classicalChainOperator Φ z ^ n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _))

end NLS.ZakharovShabat
