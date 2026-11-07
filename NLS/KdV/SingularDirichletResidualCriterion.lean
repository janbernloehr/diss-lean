import NLS.KdV.SingularDirichletPencil
import NLS.SequenceSpaces.SobolevModeDualExt

/-! # Constant residual coefficients characterize the complete native weak equation

Full H1 duality promotes all signed mode tests to the entire original test
space. The resulting condition retains precisely endpoint evaluation.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- Constancy at every original even mode suffices for the full native
Dirichlet eigen-equation, including all zero-trace H1 tests. -/
theorem singularDirichlet_eigen_iff_residual_coefficients_constant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f ↔
      ∀ n : ℤ, (singularHillOperator q (unitDirichletOriginalH1 f)-
        lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (2*n)) =
          (singularHillOperator q (unitDirichletOriginalH1 f)-
            lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode 0) := by
  constructor
  · intro he n
    exact singularDirichlet_eigen_residual_coefficients q lambda f he n
  · intro he
    apply (singularDirichletOperator_eigen_iff_boundary_defect q lambda f).mpr
    apply scalarMode_dual_ext
    intro n
    rw [singularDirichletResidual_mode]
    change _ = singularDirichletResidual q lambda f (scalarMode 0 1)*
      unitDirichletTrace (scalarMode n 1)
    rw [unitDirichletTrace_scalarMode, mul_one, singularDirichletResidual_mode, mul_zero]
    exact he n

end NLS.KdV
