import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralLocalFlow
import NLS.KdV.HillRealSpectralInvariants
import NLS.FunctionalAnalysis.CompactInvariantCurveContinuation

/-! The exact original isospectral compactness theorem supplies compact
discriminant fibers in the unchanged physical real mean-zero native
Banach space. This is a topological transfer, with no Poisson Miura map. -/
noncomputable section
open Set NLS.KdV NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

def originalHillPotentialOfRealSource (q : HillRealMeanZeroSource) : OriginalHminusOnePotential :=
  ⟨periodOneOriginal (hillRealMeanZeroInclusion q),
    (periodOneOriginal_source_iff _).mpr ⟨q.property,q.val.property⟩⟩

theorem originalHillPotentialOfRealSource_coefficients (q : HillRealMeanZeroSource) :
    originalPeriodOneCoefficients (originalHillPotentialOfRealSource q)=hillRealMeanZeroInclusion q :=
  periodOneOriginalExtract_original _

theorem originalHillRealMeanZeroSource_ofRealSource (q : HillRealMeanZeroSource) :
    originalHillRealMeanZeroSource (originalHillPotentialOfRealSource q)=q := by
  apply hillRealMeanZeroInclusion_injective
  rw [originalHillRealMeanZeroSource_inclusion,originalHillPotentialOfRealSource_coefficients]

theorem originalHillPotentialOfRealSource_ofOriginal (q : OriginalHminusOnePotential) :
    originalHillPotentialOfRealSource (originalHillRealMeanZeroSource q)=q := by
  apply Subtype.ext
  exact periodOneOriginal_originalPeriodOneCoefficients q

theorem continuous_originalHillRealMeanZeroSource : Continuous originalHillRealMeanZeroSource := by
  have he (q : OriginalHminusOnePotential) : originalHillRealMeanZeroSource q=
      hillRealMeanZeroProjection (originalPeriodOneCoefficients q) := by
    apply hillRealMeanZeroInclusion_injective
    rw [originalHillRealMeanZeroSource_inclusion,hillRealMeanZeroProjection_inclusion _
      (originalPeriodOneCoefficients_real q) (originalPeriodOneCoefficients_mean_zero q)]
  have hc : Continuous (fun q : OriginalHminusOnePotential =>
      hillRealMeanZeroProjection (originalPeriodOneCoefficients q)) :=
    hillRealMeanZeroProjection.continuous.comp (periodOneOriginalExtract.continuous.comp continuous_subtype_val)
  exact hc.congr (fun q => (he q).symm)

theorem hillRealDiscriminantData_original (q : OriginalHminusOnePotential) :
    hillRealDiscriminantData (originalHillRealMeanZeroSource q)=originalHillDiscriminant q := rfl

theorem isCompact_hillRealDiscriminant_fiber (q : HillRealMeanZeroSource) :
    IsCompact {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q} := by
  have he : {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q}=
      originalHillRealMeanZeroSource '' originalIsospectralSet (originalHillPotentialOfRealSource q) := by
    ext p
    constructor
    · intro hp
      refine ⟨originalHillPotentialOfRealSource p,?_,originalHillRealMeanZeroSource_ofRealSource p⟩
      apply (mem_originalIsospectralSet_iff_discriminant_eq _ _).mpr
      rw [← hillRealDiscriminantData_original,← hillRealDiscriminantData_original,
        originalHillRealMeanZeroSource_ofRealSource,originalHillRealMeanZeroSource_ofRealSource]
      exact hp
    · rintro ⟨r,hr,rfl⟩
      have hd := (mem_originalIsospectralSet_iff_discriminant_eq _ _).mp hr
      change hillRealDiscriminantData (originalHillRealMeanZeroSource r)=hillRealDiscriminantData q
      rw [hillRealDiscriminantData_original,hd,← hillRealDiscriminantData_original,
        originalHillRealMeanZeroSource_ofRealSource]
  rw [he]
  exact (isCompact_originalIsospectralSet _).image continuous_originalHillRealMeanZeroSource

def originalHillNativeSpectralSystem (k : ℕ+) : CompactInvariantVectorField HillRealMeanZeroSource (ℂ → ℂ) where
  field := hillRealDirichletSpectralVector k
  contDiff := contDiff_hillRealDirichletSpectralVector k
  invariant := hillRealDiscriminantData
  compact_fiber := isCompact_hillRealDiscriminant_fiber
  conserved := hillRealDiscriminantData_eq_on_integralCurve k

end NLS.Articles.KdVPseudomeasures
