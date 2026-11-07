import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRealInverse
import NLS.FunctionalAnalysis.AnalyticLocalHomeomorph

/-! The actual physical real native map is a local homeomorphism and
an open map in the original Hminus-one and signed minus-half Banach norms. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillPhysicalNativeMap_isLocalHomeomorph : IsLocalHomeomorph hillRealSignedMap := by
  exact NLS.FunctionalAnalysis.isLocalHomeomorph_of_analytic_equiv_fderiv hillRealSignedMap
    analyticAt_hillRealSignedMap hillPhysicalNativeJacobianEquiv
    (fun q => (hillPhysicalNativeJacobianEquiv_toContinuousLinearMap q).symm)

theorem hillPhysicalNativeMap_isOpenMap : IsOpenMap hillRealSignedMap :=
  hillPhysicalNativeMap_isLocalHomeomorph.isOpenMap

theorem hillPhysicalNativeMap_open_range : IsOpen (range hillRealSignedMap) := by
  simpa only [image_univ] using hillPhysicalNativeMap_isOpenMap univ isOpen_univ

end NLS.Articles.KdVPseudomeasures
