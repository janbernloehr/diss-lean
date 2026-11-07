import NLS.Articles.KdVPseudomeasures.OriginalBanachHillPeriodMap
import NLS.KdV.HillProductEquationRealDiagonal

/-! Actual original real Hill period Jacobians have no zero diagonal
entry, simultaneously for every numerator and row index on one source
patch. This prerequisite does not assert invertibility of the operator. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_Hill_period_patch_nonzero_real_diagonal (q₀ : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q₀ ∈ P.source ∧
      P.parent.center = originalPeriodOneCoefficients q₀ ∧ IsOpen P.inputDomain ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (P.equation n) P.inputDomain ∧
        AnalyticOnNhd ℂ (P.sequenceJacobian n) P.inputDomain) ∧
      ∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ P.source →
        ∀ n m : ℕ+, P.sequenceJacobian n
          (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) (lp.single 2 m 1) m ≠ 0 := by
  obtain ⟨P,hq,hcenter⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q₀)
    (originalPeriodOneCoefficients_real q₀)
  refine ⟨P,hq,hcenter,P.inputDomain_open,
    (fun n => ⟨P.analytic_equation n,P.analytic_sequenceJacobian n⟩),?_⟩
  intro q hq n m
  exact P.sequenceJacobian_actual_real_diagonal_ne_zero n m (originalPeriodOneCoefficients q)
    hq (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
