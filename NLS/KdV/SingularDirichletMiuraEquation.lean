import NLS.KdV.SingularDirichletPencil
import NLS.KdV.SingularHillMiuraPeriodOne

/-! # The native Dirichlet Miura equation with its endpoint defect

The original L2 quasi-derivative is defined before using the weak eigen-equation.
Its unit-period coefficients are transported to the unchanged original period-two
factorization. Testing only with zero-trace functions leaves the central residual
as an explicit constant in the first-order coefficient equation.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- The literal unit-period quasi-derivative, with its physical factor two. -/
def unitDirichletQuasiDerivative (u : Coeff 2) (f : UnitDirichletH1) : Coeff 2 :=
  (2:ℂ) • derivative f.val-potentialMul (by norm_num) u f.val

/-- Even insertion commutes with the full H1 multiplier. -/
theorem potentialMul_periodDoubleSobolev (u : Coeff 2) (f : ScalarDomain 2) :
    potentialMul (by norm_num) (Coeff.periodDouble u) (Coeff.periodDoubleSobolev f) =
      Coeff.periodDouble (potentialMul (by norm_num) u f) := by
  have hw : WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (Coeff.periodDoubleSobolev f) =
      Coeff.periodDouble (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) f) := by
    ext n
    rw [WeightedCoeff.sobolevToL1CLM_apply, Coeff.periodDoubleSobolev_apply]
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he, Coeff.periodDouble_even, Coeff.periodDouble_even,
        scalarInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply]
    · have he : n = 2*(n/2)+1 := by omega
      rw [he, Coeff.periodDouble_odd, Coeff.periodDouble_odd]
  change Coeff.convolution (Coeff.periodDouble u)
    (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (Coeff.periodDoubleSobolev f)) = _
  rw [hw, ← Coeff.periodDouble_convolution]
  rfl

/-- The coefficient quasi-derivative is the identical original physical one. -/
theorem periodDouble_unitDirichletQuasiDerivative (u : Coeff 2) (f : UnitDirichletH1) :
    Coeff.periodDouble (unitDirichletQuasiDerivative u f) =
      singularHillQuasiDerivative (Coeff.periodDouble u) (Coeff.periodDoubleSobolev f.val) := by
  unfold unitDirichletQuasiDerivative singularHillQuasiDerivative
  rw [map_sub, Coeff.derivative_periodDoubleSobolev, potentialMul_periodDoubleSobolev]

/-- The actual central residual, retained as the boundary-defect coefficient. -/
def unitDirichletMiuraDefect (u : Coeff 2) (lambda : ℂ) (f : UnitDirichletH1) : ℂ :=
  (singularHillOperator (periodOneOriginal (periodOneMiura u)) (unitDirichletOriginalH1 f)-
    lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode 0)

/-- A native Miura Dirichlet eigenvector satisfies the full weak first-order
coefficient equation, with its original endpoint defect and no periodicity of G. -/
theorem unitDirichletMiura_eigen_weak_equation (u : Coeff 2) (lambda : ℂ)
    (f : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
      lambda • singularDirichletDomainInclusion f) (n : ℤ) :
    2*I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      -(∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k)-lambda*f.val.val n-
        unitDirichletMiuraDefect u lambda f := by
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
  have hd := singularDirichlet_eigen_residual_coefficients
    (periodOneOriginal (periodOneMiura u)) lambda f he (-n)
  rw [show 2*(-n) = -(2*n) by ring] at hd
  change (singularHillOperator (periodOneOriginal (periodOneMiura u))
    (unitDirichletOriginalH1 f)).val (mode (-(2*n)))-
      lambda*(singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (-(2*n))) =
        unitDirichletMiuraDefect u lambda f at hd
  rw [singularHillDomainInclusion_coefficient, unitDirichletOriginalH1_coefficient,
    Coeff.periodDouble_even, scalarInclusion_apply] at hd
  push_cast at hrow
  linear_combination hrow-hd

end NLS.KdV
