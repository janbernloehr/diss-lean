import NLS.Articles.KdVPseudomeasures.OriginalAnalyticHillZeroCoefficients
import NLS.KdV.HminusOneHillPsiZeroSequenceContinuity

/-! Actual original real zero sequences are continuous in the full
literal h-minus-one sequence norm. Pairwise complex coefficient
analyticity does not yet give complex Banach sequence analyticity. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

def originalHillPsiZeroDisplacement (n : ℕ+) (q : OriginalHminusOnePotential) : lp (fun _ : ℕ+ => ℂ) 2 :=
  hillHminusPsiZeroDisplacement n ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩

theorem originalHillPsiZeroDisplacement_apply (n m : ℕ+) (q : OriginalHminusOnePotential) :
    originalHillPsiZeroDisplacement n q m =
      ((originalHillPsiRealZero n m q:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) := rfl

theorem continuous_originalHillPsiZeroDisplacement (n : ℕ+) : Continuous (originalHillPsiZeroDisplacement n) := by
  have hmap : Continuous (fun q : OriginalHminusOnePotential =>
      (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ :
        {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a})) :=
    (periodOneOriginalExtract.continuous.comp continuous_subtype_val).subtype_mk
      (fun q => originalPeriodOneCoefficients_real q)
  exact (continuous_hillHminusPsiZeroDisplacement n).comp hmap

end NLS.Articles.KdVPseudomeasures
