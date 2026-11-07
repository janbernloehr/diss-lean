import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodUniformDiagonal
import NLS.KdV.HillProductEquationFamilyCompact

/-! The entire actual original real Hill period Jacobian family has
compact closure in operator norm, retaining every positive numerator
index. Invertibility of escaping-index limits remains a separate proof. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_period_Jacobian_family_compact_closure (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    IsCompact (closure (range (fun n : ℕ+ => P.sequenceJacobian n
      (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)))) :=
  P.sequenceJacobian_actual_real_family_compact_closure (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem exists_original_Hill_period_Jacobian_uniform_operator_norm_bound (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ‖P.sequenceJacobian n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q)‖ ≤ M :=
  P.exists_actual_real_uniform_operator_norm_bound (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem exists_original_Hill_period_Jacobian_norm_convergent_subseq (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) (f : ℕ → ℕ+) :
    ∃ T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => P.sequenceJacobian (f (σ j))
          (originalHillPsiZeroDisplacement (f (σ j)) q,originalPeriodOneCoefficients q)) atTop (𝓝 T) :=
  P.exists_actual_real_sequenceJacobian_norm_convergent_subseq (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) f

end NLS.Articles.KdVPseudomeasures
