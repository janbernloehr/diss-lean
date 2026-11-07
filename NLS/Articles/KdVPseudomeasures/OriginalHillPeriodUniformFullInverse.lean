import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodEscapingLimit
import NLS.KdV.HillPeriodJacobianUniformInverse

/-! The ACTUAL FULL original real Hill period Jacobian inverses have
ONE operator-norm bound BEFORE ALL numerator indices at EVERY real
physical potential. Source-local uniformity and a common complex zero
sequence neighborhood remain separate obligations. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_full_Hill_period_limit_kernel_injective (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : d ∈ hillHminusEnergyGapData ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : P.fullEnergyPeriodJacobianEntries (originalPeriodOneCoefficients q) hq d T) : Function.Injective T :=
  P.fullEnergyPeriodJacobian_injective (originalPeriodOneCoefficients q) hq (originalPeriodOneCoefficients_real q) d hd T hT

theorem original_Hill_period_Jacobian_closure_Banach_inverse (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : T ∈ closure (range (fun n : ℕ+ => P.sequenceJacobian n
      (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)))) :
    ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2, e.toContinuousLinearMap = T := by
  have hbij := P.sequenceJacobian_actual_real_closure_bijective (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) T hT
  exact ⟨ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2),rfl⟩

theorem original_Hill_period_Jacobian_uniform_Banach_inverse_bound (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        e.toContinuousLinearMap = P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) ∧
        ‖e.symm.toContinuousLinearMap‖ ≤ M :=
  P.exists_actual_real_uniform_sequenceJacobian_equiv (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_period_Jacobian_uniform_bounded_inverse (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)).comp R = ContinuousLinearMap.id ℂ _ ∧
        R.comp (P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)) = ContinuousLinearMap.id ℂ _ ∧
        ‖R‖ ≤ M :=
  P.exists_actual_real_uniform_sequenceJacobian_inverse (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem exists_original_uniform_Hill_period_inverse_patch (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
        ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
          e.toContinuousLinearMap = P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ M := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  exact ⟨P,hq,original_Hill_period_Jacobian_uniform_Banach_inverse_bound P q hq⟩

end NLS.Articles.KdVPseudomeasures
