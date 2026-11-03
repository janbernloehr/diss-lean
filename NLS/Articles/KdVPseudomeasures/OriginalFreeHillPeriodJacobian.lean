import NLS.Articles.KdVPseudomeasures.OriginalHillProductJacobian
import NLS.KdV.HillFreePeriodOperator

/-! The original inverse-index weighted Hill period equations at the
free source. Genuine positive-gap circles are selected before ALL
numerator indices, and all derivative rows are those of ONE bounded
identity with inverse norm one. This does not assert a nonlinear
sequence-valued period map or a Jacobian inverse at nonzero sources.
The diagonal product period pi*n/2 is proved here ONLY at the free source. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_free_Hill_product_period (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D 0 =
      if m = n then (Real.pi:ℂ)*(n:ℕ)/2 else 0 :=
  hillEnergyProductFixedPeriod_free n m D

theorem original_free_Hill_period_derivative (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    fderiv ℂ (hillFreePeriodEquationRow n m D) 0 =
      lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m :=
  hillFreePeriodEquationRow_fderiv_eq_eval n m D

theorem exists_original_free_Hill_period_Jacobian :
    ∃ D : ∀ m : ℕ+, SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
        (0:CoeffPair 2) ((m:ℕ):ℤ),
    ∃ J : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      ‖J.toContinuousLinearMap‖ = 1 ∧ ‖J.symm.toContinuousLinearMap‖ = 1 ∧
      ∀ n m : ℕ+, hillFreePeriodEquationRow n m (D m) 0 = 0 ∧
        AnalyticOnNhd ℂ (hillFreePeriodEquationRow n m (D m)) univ ∧
        ∀ h : lp (fun _ : ℕ+ => ℂ) 2,
          fderiv ℂ (hillFreePeriodEquationRow n m (D m)) 0 h = J h m := by
  refine ⟨hillFreePeriodCircle,hillFreePeriodJacobianEquiv,?_,
    norm_hillFreePeriodJacobianInverse,?_⟩
  · change ‖hillFreePeriodJacobianOperator‖ = 1
    exact norm_hillFreePeriodJacobianOperator
  · intro n m
    refine ⟨hillFreePeriodEquationRow_zero n m _,?_,?_⟩
    · intro d _
      exact analyticAt_hillFreePeriodEquationRow n m _ d
    · intro h
      exact hillFreePeriodJacobianOperator_rows n m _ h

end NLS.Articles.KdVPseudomeasures
