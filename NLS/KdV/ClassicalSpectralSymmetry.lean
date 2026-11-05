import NLS.KdV.ConstantUpperSpectralBridge

/-! # The actual constant-upper trace depends only on spectral energy

A constant triangular change of state intertwines the original constructed
ZS systems at z and w whenever z^2=w^2. IVP uniqueness proves the solution
identity. Thus the scalar Hill trace, rather than an assumed spectral
function, descends through the energy variable lambda=z^2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Change ZS spectral coordinate while retaining scalar position/derivative. -/
def constantUpperSpectralTransition (z w : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (ContinuousLinearMap.snd ℂ ℂ ℂ + (z-w) • ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem constantUpperSpectralTransition_apply (z w : ℂ) (v : ℂ × ℂ) :
    constantUpperSpectralTransition z w v = (v.1, v.2+(z-w)*v.1) := rfl

/-- The first-order physical systems intertwine at equal scalar energies. -/
theorem constantUpperSpectralTransition_ode (q z w : ℂ) (v : ℂ × ℂ)
    (he : z^2 = w^2) :
    classicalODECoefficient (-1,-q) w (constantUpperSpectralTransition z w v) =
      constantUpperSpectralTransition z w (classicalODECoefficient (-1,-q) z v) := by
  apply Prod.ext
  · simp only [classicalODECoefficient_apply, constantUpperSpectralTransition_apply]
    ring
  · simp only [classicalODECoefficient_apply, constantUpperSpectralTransition_apply]
    linear_combination I*v.1*he

/-- The actual IVP solutions transform at equal energies; no spectral
symmetry or monodromy identity is assumed. -/
theorem classicalSolution_constantUpper_transition (q : NLS.LinearVolterra.Curve ℂ)
    (z w : ℂ) (he : z^2 = w^2) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    constantUpperSpectralTransition z w (classicalSolution (constantUpperPotential q) z v t) =
      classicalSolution (constantUpperPotential q) w (constantUpperSpectralTransition z w v) t := by
  apply classicalSolution_unique (constantUpperPotential q) w
    (constantUpperSpectralTransition z w v)
    (fun x => constantUpperSpectralTransition z w (classicalSolution (constantUpperPotential q) z v x))
    ((constantUpperSpectralTransition z w).continuous.comp
      (continuous_classicalSolution (constantUpperPotential q) z v)).continuousOn
    (by rw [classicalSolution_zero]) _ t.property
  intro s _
  have hs := hasDerivAt_classicalSolution (constantUpperPotential q) z v s
  have hd := (HasFDerivAt.hasDerivAt hs.fst).prodMk
    ((HasFDerivAt.hasDerivAt hs.snd).add
      ((HasFDerivAt.hasDerivAt hs.fst).const_mul (z-w)))
  have hcoeff := constantUpperSpectralTransition_ode (q s) z w
    (classicalSolution (constantUpperPotential q) z v s) he
  rw [← constantUpperPotential_apply q s] at hcoeff
  rw [hcoeff]
  simpa [constantUpperSpectralTransition_apply] using! hd

/-- The actual classical discriminant is constant on the fibers of z^2. -/
theorem classicalDiscriminant_constantUpper_eq_of_sq_eq
    (q : NLS.LinearVolterra.Curve ℂ) (z w : ℂ) (he : z^2 = w^2) :
    classicalDiscriminant (constantUpperPotential q) z =
      classicalDiscriminant (constantUpperPotential q) w := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h1 := classicalSolution_constantUpper_transition q z w he (1,0) t
  have h2 := classicalSolution_constantUpper_transition q z w he (0,1) t
  rw [classicalSolution_eq_columns (constantUpperPotential q) w
    (constantUpperSpectralTransition z w (1,0)) t] at h1
  have h1f := congrArg Prod.fst h1
  have h2f := congrArg Prod.fst h2
  have h2s := congrArg Prod.snd h2
  simp only [constantUpperSpectralTransition_apply, Prod.fst_add,
    Prod.smul_fst, smul_eq_mul, mul_one, mul_zero, add_zero, one_smul, zero_add] at h1f h2f h2s
  simp only [classicalDiscriminant, classicalMonodromy, classicalFundamentalMatrix,
    Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  dsimp [t] at h1f h2f h2s
  linear_combination h1f + h2s - (z-w)*h2f

/-- In particular the actual trace is even in the square-root parameter. -/
theorem classicalDiscriminant_constantUpper_even (q : NLS.LinearVolterra.Curve ℂ) :
    Function.Even (classicalDiscriminant (constantUpperPotential q)) := by
  intro z
  exact classicalDiscriminant_constantUpper_eq_of_sq_eq q (-z) z (by ring)

/-- The normalized scalar Hill solutions have the same energy symmetry. -/
theorem constantUpperHillTrace_eq_of_sq_eq (q : NLS.LinearVolterra.Curve ℂ)
    (z w : ℂ) (he : z^2 = w^2) : constantUpperHillTrace q z = constantUpperHillTrace q w := by
  simp only [constantUpperHillTrace_eq_discriminant]
  exact classicalDiscriminant_constantUpper_eq_of_sq_eq q z w he

end NLS.KdV
