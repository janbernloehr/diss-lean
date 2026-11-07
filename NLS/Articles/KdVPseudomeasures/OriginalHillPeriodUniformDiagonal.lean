import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodInverse
import NLS.KdV.HillProductEquationUniformDiagonalTail
import NLS.KdV.HillProductEquationUniformDiagonalInverse

/-! The original physical real Hill period diagonals have one high-row
cutoff and one inverse norm bound before ALL numerator indices. Uniform
bounds for the full inverse and a common complex zero-sequence source
domain remain separate obligations. -/
noncomputable section
open Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_period_Jacobian_uniform_diagonal_tail (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n m : ℕ+, N ≤ (m:ℕ) →
      ‖P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
        (lp.single 2 m 1) m-1‖ < ε :=
  P.sequenceJacobian_actual_real_uniform_diagonal_tail (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) ε hε

theorem original_Hill_period_Jacobian_uniform_diagonal_lower (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n m : ℕ+,
      δ ≤ ‖P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
        (lp.single 2 m 1) m‖ :=
  P.sequenceJacobian_actual_real_uniform_diagonal_lower (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_period_Jacobian_uniform_diagonal_inverse (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ D : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        D.toContinuousLinearMap = NLS.LpSequence.positiveOperatorDiagonal
          (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)) ∧
        (∀ a m, D.symm a m =
          (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
            (lp.single 2 m 1) m)⁻¹*a m) ∧ ‖D.symm.toContinuousLinearMap‖ ≤ M :=
  P.exists_actual_real_uniform_diagonal_inverse (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
