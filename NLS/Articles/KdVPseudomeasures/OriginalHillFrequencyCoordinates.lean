import NLS.Articles.KdVPseudomeasures.OriginalJointHillPeriodEquations
import NLS.KdV.HillProductPlacementDomain

/-! ONE open analytic independent-energy frequency domain contains
ALL actual original real Hill zero sequences. Exact quadratic product
algebra and uniform original-circle coordinate bounds are shared in the
library. No source-to-zero sequence analyticity or universal product
prefactor is assumed. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_common_Hill_frequency_coordinates (q : OriginalHminusOnePotential) :
    ∃ B : HillHminusPsiBall, B.center = originalPeriodOneCoefficients q ∧
      originalPeriodOneCoefficients q ∈ B.source ∧
    ∃ Ω : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2), IsOpen Ω ∧
      AnalyticOnNhd ℂ hillIndependentFrequencyDisplacement Ω ∧
      (∀ n : ℕ+, ((B.parent.miuraBall.actionBall.shift:ℂ),originalHillPsiZeroDisplacement n q) ∈ Ω) ∧
      (∀ t ∈ Ω, ‖hillIndependentFrequencyDisplacement t‖ ≤ 2*Real.pi⁻¹*(‖t.2‖+2*‖t.1‖)) ∧
      ∀ (n : ℕ+) (k : ℤ),
        hillIndependentFrequency ((B.parent.miuraBall.actionBall.shift:ℂ),originalHillPsiZeroDisplacement n q) k ∈
          sourcePeriodicSegment (by norm_num) (by norm_num)
            (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) k := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,_,hB,hq⟩ := exists_hillHminusPsiBall A (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  exact ⟨B,hB,hq,LpSequence.quadraticFrequencyDomain Real.pi,
    LpSequence.isOpen_quadraticFrequencyDomain Real.pi Real.pi_pos,
    analyticOnNhd_hillIndependentFrequencyDisplacement,
    (fun n => B.actual_zero_data_mem_frequencyDomain n _ hq (originalPeriodOneCoefficients_real q)),
    (fun t _ => norm_hillIndependentFrequencyDisplacement_le t),
    (fun n k => B.actual_independentFrequency_mem_signed_gap n _ hq (originalPeriodOneCoefficients_real q) k)⟩

end NLS.Articles.KdVPseudomeasures
