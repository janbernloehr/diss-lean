import NLS.Articles.KdVPseudomeasures.OriginalHillNumeratorProduct
import NLS.Articles.KdVPseudomeasures.OriginalHillZeroSequenceTopology
import NLS.KdV.HminusOneHillPsiProductDensity

/-! Original real-source Hill products are jointly continuous in energy
and the original physical H-minus-one source norm. Their actual unique
nonzero scalar is continuous in that same source norm. Joint entire
dependence on independent energy/sequence data is proved in the shared
library; complex source sequence analyticity and the universal scalar
normalization remain open. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

def originalHillPsiLiteralProduct (n : ℕ+) (t : ℂ × OriginalHminusOnePotential) : ℂ :=
  hillEnergySequenceProduct n (t.1,originalHillPsiZeroDisplacement n t.2)

theorem continuous_originalHillPsiLiteralProduct (n : ℕ+) : Continuous (originalHillPsiLiteralProduct n) := by
  have hprod : Continuous (hillEnergySequenceProduct n) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticAt_hillEnergySequenceProduct n t).continuousAt)
  exact hprod.comp (continuous_fst.prodMk ((continuous_originalHillPsiZeroDisplacement n).comp continuous_snd))

theorem original_Hill_numerator_eq_scalar_mul_literalProduct (n : ℕ+) (E : ℂ)
    (q : OriginalHminusOnePotential) : hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q) =
      originalHillPsiProductScalar n q*originalHillPsiLiteralProduct n (E,q) :=
  hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n E
    ⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩

theorem continuous_originalHillPsiProductScalar (n : ℕ+) : Continuous (originalHillPsiProductScalar n) := by
  change Continuous (fun q : OriginalHminusOnePotential =>
    hillHminusPsiProductScalar n (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q))
  have hmap : Continuous (fun q : OriginalHminusOnePotential =>
      (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ : PeriodOneRealHminusOne)) :=
    (periodOneOriginalExtract.continuous.comp continuous_subtype_val).subtype_mk
      (fun q => originalPeriodOneCoefficients_real q)
  have H := Continuous.comp
    (f := fun q : OriginalHminusOnePotential =>
      (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ : PeriodOneRealHminusOne))
    (g := fun a : PeriodOneRealHminusOne => hillHminusPsiProductScalar n a.val a.property)
    (continuous_hillHminusPsiProductScalar n) hmap
  refine H.congr ?_
  intro q
  rfl

end NLS.Articles.KdVPseudomeasures
