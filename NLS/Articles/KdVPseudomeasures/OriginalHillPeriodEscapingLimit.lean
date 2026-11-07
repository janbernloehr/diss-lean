import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodFamilyCompact
import NLS.KdV.HillProductEquationEscapingLimit

/-! Exact full-product identification of escaping real Hill period
Jacobian limits on the original physical source and energy-gap data.
Invertibility of the full-product limit still requires proof. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_full_energy_gap_data_compact (q : OriginalHminusOnePotential) :
    IsCompact (hillHminusEnergyGapData ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩) :=
  isCompact_hillHminusEnergyGapData _

theorem original_escaping_Hill_period_Jacobian_limit_identification (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hT : Tendsto (fun j => P.sequenceJacobian (n j)
      (originalHillPsiZeroDisplacement (n j) q,originalPeriodOneCoefficients q)) atTop (𝓝 T)) :
    ∃ d ∈ hillHminusEnergyGapData ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩,
      P.fullEnergyPeriodJacobianEntries (originalPeriodOneCoefficients q) hq d T ∧
        ∀ m : ℕ+, hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ)
          (P.sourcePsi (originalPeriodOneCoefficients q))
          (P.canonicalPeriodCircle (originalPeriodOneCoefficients q) hq ((m:ℕ):ℤ)) d = 0 :=
  P.exists_full_energy_gap_data_of_actual_real_escaping_limit (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) n hn T hT

theorem exists_original_joint_escaping_Hill_period_limit (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop) :
    ∃ T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      ∃ d ∈ hillHminusEnergyGapData ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩,
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun j => P.sequenceJacobian (n (σ j))
            (originalHillPsiZeroDisplacement (n (σ j)) q,originalPeriodOneCoefficients q)) atTop (𝓝 T) ∧
          Tendsto (fun j => originalHillPsiZeroDisplacement (n (σ j)) q) atTop (𝓝 d) ∧
          P.fullEnergyPeriodJacobianEntries (originalPeriodOneCoefficients q) hq d T ∧
          ∀ m : ℕ+, hillEnergyFullProductFixedPeriod (P.parent.parent.miuraBall.actionBall.shift:ℂ)
            (P.sourcePsi (originalPeriodOneCoefficients q))
            (P.canonicalPeriodCircle (originalPeriodOneCoefficients q) hq ((m:ℕ):ℤ)) d = 0 :=
  P.exists_actual_real_joint_escaping_limit (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q) n hn

end NLS.Articles.KdVPseudomeasures
