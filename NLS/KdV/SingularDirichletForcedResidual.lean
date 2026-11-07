import NLS.KdV.SingularDirichletDenseDomain
import NLS.KdV.SingularDirichletMiuraConverse

/-! # Full native inhomogeneous residuals and the retained boundary defect

Forcing by a native domain vector is kept as an actual full-dual mass form.
The annihilator of zero-trace tests remains the endpoint trace functional.
The resulting coefficient equation includes the forcing and boundary jump;
neither can be discarded when constructing algebraic root chains.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- The native mass form before restricting the full unit-period dual. -/
theorem unitHillMassDual_restriction (g : UnitDirichletH1) :
    unitDirichletDualRestriction (unitHillMassDual g.val) = singularDirichletDomainInclusion g := by
  rw [singularDirichletDomainInclusion_eq_restricted_mass]
  rfl

/-- The actual forced residual on the full unit-period H1 test space. -/
def singularDirichletForcedResidual
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f g : UnitDirichletH1) :
    ScalarDomain 2 →L[ℂ] ℂ :=
  singularDirichletResidual q lambda f-unitHillMassDual g.val

/-- Its exact restriction is the actual inhomogeneous native equation. -/
theorem singularDirichletForcedResidual_restriction
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f g : UnitDirichletH1) :
    unitDirichletDualRestriction (singularDirichletForcedResidual q lambda f g) =
      singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f-
        singularDirichletDomainInclusion g := by
  rw [singularDirichletForcedResidual, map_sub, singularDirichletResidual_restriction,
    unitHillMassDual_restriction]

/-- Each signed raw mode reads the entire original residual and forcing. -/
theorem singularDirichletForcedResidual_mode
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f g : UnitDirichletH1) (n : ℤ) :
    singularDirichletForcedResidual q lambda f g (scalarMode n 1) =
      (singularHillOperator q (unitDirichletOriginalH1 f)-
        lambda • singularHillDomainInclusion (unitDirichletOriginalH1 f)).val (mode (2*n))-
          g.val.val (-n) := by
  change singularDirichletResidual q lambda f (scalarMode n 1)-
    unitHillMassDual g.val (scalarMode n 1) = _
  rw [singularDirichletResidual_mode]
  congr 1
  change WeightedCoeff.sobolevBilinearPairing 1 (scalarMode n 1) (unitHillMass g.val) = _
  rw [WeightedCoeff.sobolevBilinearPairing_apply]
  simp only [scalarMode_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq, unitHillMass_coefficient]

/-- Inhomogeneous native equations are equivalent to the full residual being
exactly a multiple of endpoint evaluation. -/
theorem singularDirichlet_forced_iff_boundary_defect
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f g : UnitDirichletH1) :
    singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f =
      singularDirichletDomainInclusion g ↔
    singularDirichletForcedResidual q lambda f g =
      singularDirichletForcedResidual q lambda f g (scalarMode 0 1) • unitDirichletTrace := by
  rw [← unitDirichletDualRestriction_eq_zero_iff, singularDirichletForcedResidual_restriction]
  exact sub_eq_zero.symm

/-- The central forced residual retains the actual quasi-derivative endpoint jump. -/
def unitDirichletMiuraForcedDefect (u : Coeff 2) (lambda : ℂ) (f g : UnitDirichletH1) : ℂ :=
  singularDirichletForcedResidual (periodOneOriginal (periodOneMiura u)) lambda f g (scalarMode 0 1)

/-- Every actual associated-vector equation gives the complete weak first-order
coefficient equation, with its forcing and its precise endpoint defect. -/
theorem unitDirichletMiura_forced_weak_equation (u : Coeff 2) (lambda : ℂ)
    (f g : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g) (n : ℤ) :
    2*Complex.I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      -(∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k)-lambda*f.val.val n-
        g.val.val n-unitDirichletMiuraForcedDefect u lambda f g := by
  have h := congrArg (fun F : ScalarDomain 2 →L[ℂ] ℂ => F (scalarMode (-n) 1))
    ((singularDirichlet_forced_iff_boundary_defect _ lambda f g).mp he)
  rw [singularDirichletForcedResidual_mode, show 2*(-n) = -(2*n) by ring,
    unitDirichletMiura_residual_coefficient] at h
  change _ = unitDirichletMiuraForcedDefect u lambda f g*unitDirichletTrace (scalarMode (-n) 1) at h
  rw [unitDirichletTrace_scalarMode, mul_one, neg_neg] at h
  linear_combination -h

/-- Conversely, every full weak coefficient equation with the forcing and
one scalar boundary defect gives the ENTIRE native inhomogeneous equation. -/
theorem singularDirichletMiura_forced_of_weak_equation (u : Coeff 2) (lambda c : ℂ)
    (f g : UnitDirichletH1)
    (h : ∀ n : ℤ, 2*Complex.I*(Real.pi:ℂ)*n*unitDirichletQuasiDerivative u f n =
      -(∑' k : ℤ, u (n-k)*unitDirichletQuasiDerivative u f k)-lambda*f.val.val n-g.val.val n-c) :
    singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g := by
  have hF : singularDirichletForcedResidual (periodOneOriginal (periodOneMiura u)) lambda f g =
      c • unitDirichletTrace := by
    apply scalarMode_dual_ext
    intro n
    rw [singularDirichletForcedResidual_mode, show 2*n = -(2*(-n)) by ring,
      unitDirichletMiura_residual_coefficient]
    change _ = c*unitDirichletTrace (scalarMode n 1)
    rw [unitDirichletTrace_scalarMode, mul_one]
    linear_combination -(h (-n))
  have hr := congrArg unitDirichletDualRestriction hF
  rw [singularDirichletForcedResidual_restriction] at hr
  have hz : unitDirichletDualRestriction (c • unitDirichletTrace) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change c*unitDirichletTrace v.val = 0
    rw [show unitDirichletTrace v.val = 0 from v.property, mul_zero]
  rw [hz] at hr
  exact sub_eq_zero.mp hr

end NLS.KdV
