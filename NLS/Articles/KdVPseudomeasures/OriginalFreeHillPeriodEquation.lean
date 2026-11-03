import NLS.Articles.KdVPseudomeasures.OriginalFreeHillPeriodJacobian
import NLS.KdV.HillFreePeriodSequenceDerivative

/-! The ACTUAL original weighted nonlinear Hill period equation at
the free source is entire into the literal inverse-index l2 space.
A single constant bounds all maps and their errors before ALL n.
Its full strict Banach derivative is the same identity with inverse
norm one. Source-joint analyticity and nonzero-source inverses are
separate remaining obligations. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open Filter Topology
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_free_Hill_nonlinear_period_equation (n : ℕ+) :
    AnalyticOnNhd ℂ (hillFreePeriodEquation n) univ ∧
    hillFreePeriodEquation n 0 = 0 ∧
    HasStrictFDerivAt (hillFreePeriodEquation n) hillFreePeriodJacobianOperator 0 ∧
    ∀ (m : ℕ+)
      (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
      (d : lp (fun _ : ℕ+ => ℂ) 2),
      hillFreePeriodEquation n d m = hillFreePeriodEquationRow n m D d :=
  ⟨fun d _ => analyticAt_hillFreePeriodEquation n d,hillFreePeriodEquation_zero n,
    hasStrictFDerivAt_hillFreePeriodEquation_zero n,hillFreePeriodEquation_apply_any_circle n⟩

theorem exists_original_free_Hill_uniform_period_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2),
      ‖hillFreePeriodEquation n d‖ ≤ Real.exp (C*‖d‖)*‖d‖ ∧
      ‖hillFreePeriodEquation n d-d‖ ≤ (Real.exp (C*‖d‖)-1)*‖d‖ :=
  ⟨hillFreeInteractionConstant,hillFreeInteractionConstant_nonneg,
    fun n d => ⟨norm_hillFreePeriodEquation_le n d,norm_hillFreePeriodEquation_sub_id_le n d⟩⟩

theorem original_free_Hill_nonlinear_period_Jacobian_inverse (n : ℕ+) :
    fderiv ℂ (hillFreePeriodEquation n) 0 = hillFreePeriodJacobianEquiv.toContinuousLinearMap ∧
    ‖hillFreePeriodJacobianEquiv.toContinuousLinearMap‖ = 1 ∧
    ‖hillFreePeriodJacobianEquiv.symm.toContinuousLinearMap‖ = 1 :=
  ⟨fderiv_hillFreePeriodEquation_zero n,norm_hillFreePeriodJacobianOperator,
    norm_hillFreePeriodJacobianInverse⟩

theorem original_free_Hill_period_equation_local_inverse (n : ℕ+) :
    ∃ G : lp (fun _ : ℕ+ => ℂ) 2 → lp (fun _ : ℕ+ => ℂ) 2,
      AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      (∀ᶠ d in 𝓝 (0:lp (fun _ : ℕ+ => ℂ) 2), G (hillFreePeriodEquation n d) = d) ∧
      (∀ᶠ e in 𝓝 (0:lp (fun _ : ℕ+ => ℂ) 2), hillFreePeriodEquation n (G e) = e) ∧
      fderiv ℂ G 0 = hillFreePeriodJacobianOperator :=
  exists_hillFreePeriodEquation_localInverse n

end NLS.Articles.KdVPseudomeasures
