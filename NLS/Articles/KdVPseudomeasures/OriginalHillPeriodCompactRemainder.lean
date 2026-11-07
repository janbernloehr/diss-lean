import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodRealDiagonal
import NLS.KdV.HillProductEquationCompactRemainder

/-! The actual original real Hill period Jacobian is a bounded
nonvanishing diagonal plus a compact remainder. The missing diagonal
lower bound and kernel injectivity remain separate proof obligations. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_period_Jacobian_diagonal_add_compact (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) (n : ℕ+) :
    ∃ D K : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      IsCompactOperator K ∧
      P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) = D+K ∧
      (∀ a m, D a m =
        P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
          (lp.single 2 m 1) m*a m) ∧
      ∀ m : ℕ+, D (lp.single 2 m 1) m ≠ 0 :=
  P.sequenceJacobian_actual_real_diagonal_add_compact (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) n

end NLS.Articles.KdVPseudomeasures
