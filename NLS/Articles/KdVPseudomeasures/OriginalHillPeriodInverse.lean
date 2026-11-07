import NLS.Articles.KdVPseudomeasures.OriginalHillPeriodInvertibleDiagonal
import NLS.KdV.HillProductEquationAnalyticZeroSequence

/-! Unconditional actual real Hill period inverses and fixed-n full
Banach analytic zero branches on the original physical source. Uniform
inverse bounds and a common source neighborhood before ALL n remain open. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_period_Jacobian_Banach_inverse (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) (n : ℕ+) :
    ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      e.toContinuousLinearMap = P.sequenceJacobian n
        (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) :=
  P.exists_actual_real_sequenceJacobian_equiv n (originalPeriodOneCoefficients q) hq
    (originalPeriodOneCoefficients_real q)

theorem exists_original_local_analytic_Hill_zero_sequence (q : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q ∈ P.source ∧
      ∀ n : ℕ+, ∃ s : PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
        AnalyticAt ℂ s (originalPeriodOneCoefficients q) ∧ s (originalPeriodOneCoefficients q) = originalHillPsiZeroDisplacement n q ∧
        (∀ᶠ y in 𝓝 (originalPeriodOneCoefficients q), (s y,y) ∈ P.inputDomain ∧ P.equation n (s y,y) = 0) ∧
        ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩,
          s a.val = hillHminusPsiZeroDisplacement n a := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  exact ⟨P,hq,fun n => P.exists_actual_analytic_zero_sequence n _ hq (originalPeriodOneCoefficients_real q)⟩

end NLS.Articles.KdVPseudomeasures
