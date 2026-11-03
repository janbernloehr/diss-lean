import NLS.KdV.SingularDirichletMiuraEquation
import NLS.KdV.SingularDirichletResidualCriterion

/-! # Sufficiency of the complete weak Miura coefficient equation

The factorization gives every coefficient of the native residual. Constancy
of all those coefficients, including the central one, gives the entire
zero-trace H1 weak eigen-equation by full Sobolev duality.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- The complete original residual formula precedes any eigen-equation. -/
theorem unitDirichletMiura_residual_coefficient (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1) (n : ℤ) :
    (singularHillOperator (periodOneOriginal (periodOneMiura u)) (unitDirichletOriginalH1 f)-
      lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (-(2*n))) =
        -(2*I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n)-
          (∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k)-lambda*f.val.val n := by
  have hfactor := singularHillOperator_miura_factorization (Coeff.periodDouble u)
    (Coeff.periodDoubleSobolev f.val)
  have hnative : scalarDomainOriginalH1 (Coeff.periodDoubleSobolev f.val) =
      unitDirichletOriginalH1 f := rfl
  rw [hnative, singularHillMiuraPotential_periodDouble,
    ← periodDouble_unitDirichletQuasiDerivative] at hfactor
  have hrow := congrArg (fun v : FourierLebesgueSpace (2:ℝ) (-1) 2 =>
    v.val (mode (-(2*n)))) hfactor
  change (singularHillOperator (periodOneOriginal (periodOneMiura u))
    (unitDirichletOriginalH1 f)).val (mode (-(2*n))) =
      -(l2DerivativeOriginalHminus (Coeff.periodDouble (unitDirichletQuasiDerivative u f))).val
        (mode (-(2*n)))-
      (l2ProductOriginalHminus (Coeff.periodDouble u)
        (Coeff.periodDouble (unitDirichletQuasiDerivative u f))).val (mode (-(2*n))) at hrow
  rw [l2DerivativeOriginalHminus_coefficient, l2ProductOriginalHminus_coefficient,
    Coeff.periodDouble_even] at hrow
  have hp := congrArg (fun a : Coeff ⊤ => a (2*n))
    (Coeff.periodDouble_youngConvolution youngRelation_two_two_top u
      (unitDirichletQuasiDerivative u f))
  have hs : (∑' k : ℤ, Coeff.periodDouble u (2*n-k)*
      Coeff.periodDouble (unitDirichletQuasiDerivative u f) k) =
        ∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k := by
    simpa only [Coeff.periodDouble_even, Coeff.youngConvolution_apply] using hp.symm
  rw [hs] at hrow
  change (singularHillOperator (periodOneOriginal (periodOneMiura u))
    (unitDirichletOriginalH1 f)).val (mode (-(2*n)))-
      lambda*(singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (-(2*n))) = _
  rw [hrow, singularHillDomainInclusion_coefficient, unitDirichletOriginalH1_coefficient,
    Coeff.periodDouble_even, scalarInclusion_apply]
  push_cast
  ring

/-- A full first-order weak coefficient equation with its actual endpoint
defect suffices for the entire native Dirichlet weak eigen-equation. -/
theorem singularDirichletMiura_eigen_of_weak_equation (u : Coeff 2) (lambda c : ℂ)
    (f : UnitDirichletH1)
    (h : ∀ n : ℤ, 2*I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      -(∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k)-lambda*f.val.val n-c) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f := by
  have hR (n : ℤ) :
      (singularHillOperator (periodOneOriginal (periodOneMiura u)) (unitDirichletOriginalH1 f)-
        lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (-(2*n))) = c := by
    rw [unitDirichletMiura_residual_coefficient]
    linear_combination -(h n)
  apply (singularDirichlet_eigen_iff_residual_coefficients_constant _ lambda f).mpr
  intro n
  rw [show 2*n = -(2*(-n)) by ring, hR]
  simpa only [mul_zero, neg_zero] using (hR 0).symm

end NLS.KdV
