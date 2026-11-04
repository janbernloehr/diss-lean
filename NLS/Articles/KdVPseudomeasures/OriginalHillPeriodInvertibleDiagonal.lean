import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodCompactRemainder
import NLS.KdV.HillProductEquationFredholmAlternative

/-! Original physical real Hill period Jacobians have an invertible
diagonal plus a compact remainder, with an exact reciprocal diagonal
inverse. Full kernel injectivity and uniformity in n remain open. -/
noncomputable section
open Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_period_Jacobian_invertible_diagonal_add_compact (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) (n : ℕ+) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ m : ℕ+, δ ≤ ‖P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
        (lp.single 2 m 1) m‖) ∧
      ∃ D : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        ∃ K : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
          IsCompactOperator K ∧
          P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) = D.toContinuousLinearMap+K ∧
          (∀ a m, D a m = P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
            (lp.single 2 m 1) m*a m) ∧
          (∀ a m, D.symm a m =
            (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)
              (lp.single 2 m 1) m)⁻¹*a m) ∧
          ‖D.symm.toContinuousLinearMap‖ ≤ δ⁻¹ :=
  P.exists_actual_real_diagonal_equiv (originalPeriodOneCoefficients q) hq (originalPeriodOneCoefficients_real q) n

theorem original_Hill_period_Jacobian_bijective_of_injective (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) (n : ℕ+)
    (hinj : Function.Injective (P.sequenceJacobian n
      (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q))) :
    Function.Bijective (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)) :=
  P.sequenceJacobian_actual_real_bijective_of_injective (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) n hinj

end NLS.Articles.KdVPseudomeasures
