import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity
import NLS.Articles.KdVPseudomeasures.ArticleEndpointTargetNorm

/-! Actual native injectivity on the ENTIRE original distribution domain
and on the full endpoint source, with unchanged physical coefficients
and the article's literal endpoint target norm. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_native_coordinates_injective (q p : OriginalHminusOnePotential)
    (hz : ∀ k : ℤ, hillHminusNativeCoordinate k (originalPeriodOneCoefficients q)=
      hillHminusNativeCoordinate k (originalPeriodOneCoefficients p)) : q=p := by
  have he : hillRealSignedMap (originalHillRealMeanZeroSource q)=
      hillRealSignedMap (originalHillRealMeanZeroSource p) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate,
      originalHillRealMeanZeroSource_inclusion,originalHillRealMeanZeroSource_inclusion]
    exact hz k
  have hc := congrArg hillRealMeanZeroInclusion (injective_hillRealSignedMap he)
  rw [originalHillRealMeanZeroSource_inclusion,originalHillRealMeanZeroSource_inclusion] at hc
  apply Subtype.ext
  calc
    q.val=periodOneOriginal (originalPeriodOneCoefficients q) :=
      (periodOneOriginal_originalPeriodOneCoefficients q).symm
    _=periodOneOriginal (originalPeriodOneCoefficients p) := congrArg periodOneOriginal hc
    _=p.val := periodOneOriginal_originalPeriodOneCoefficients p

theorem endpointPhysicalNativeSourceInclusion_injective (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (endpointPhysicalNativeSourceInclusion r hr) := by
  intro q p he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have hc := congrArg (fun a : HillRealMeanZeroSource => a.val.val.val k) he
  simpa only [endpointPhysicalNativeSourceInclusion_apply] using hc

theorem injective_hillEndpointRealSignedMap (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (hillEndpointRealSignedMap r hr) := by
  intro q p he
  apply endpointPhysicalNativeSourceInclusion_injective r hr
  apply injective_hillRealSignedMap
  rw [← endpointPhysicalNativeTargetInclusion_map,← endpointPhysicalNativeTargetInclusion_map,he]

theorem injective_articleEndpointPhysicalMap (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (articleEndpointPhysicalMap r hr) := by
  intro q p he
  apply injective_hillEndpointRealSignedMap r hr
  exact (articleEndpointTargetEquiv r hr).injective he

theorem injective_articleEndpointCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (articleEndpointCoordinates r hr) := by
  intro q p he
  apply (originalEndpointRealSourceEquiv r hr).injective
  apply injective_articleEndpointPhysicalMap r hr
  exact he

end NLS.Articles.KdVPseudomeasures
