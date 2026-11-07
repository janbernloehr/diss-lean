import NLS.Articles.KdVPseudomeasures.OriginalHillL2NativeInverse
import NLS.FunctionalAnalysis.InverseGermDerivative
import NLS.FunctionalAnalysis.AnalyticLocalHomeomorph

/-! The ACTUAL original L2-to-positive-half map has an invertible bounded
real derivative and is a local homeomorphism in these genuine norms. -/
noncomputable section
open Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillL2NativeMap_derivative_equiv (u : HillRealL2BanachSource) :
    ∃ e : HillRealL2BanachSource ≃L[ℝ] HillRealSignedHalfTarget,
      e.toContinuousLinearMap=fderiv ℝ hillL2NativeMap u := by
  obtain ⟨G,hG,hGu,hl,hr⟩ := exists_hillL2NativeMap_localInverse u
  obtain ⟨e,he,_⟩ := @NLS.FunctionalAnalysis.exists_fderiv_equiv_of_inverse_germs ℝ
    HillRealL2BanachSource HillRealSignedHalfTarget inferInstance inferInstance inferInstance inferInstance inferInstance
    hillL2NativeMap G u (analyticAt_hillL2NativeMap u).differentiableAt hG.differentiableAt hGu hl hr
  exact ⟨e,he⟩

def hillL2NativeJacobianEquiv (u : HillRealL2BanachSource) :
    HillRealL2BanachSource ≃L[ℝ] HillRealSignedHalfTarget :=
  (exists_hillL2NativeMap_derivative_equiv u).choose

theorem hillL2NativeJacobianEquiv_toContinuousLinearMap (u : HillRealL2BanachSource) :
    (hillL2NativeJacobianEquiv u).toContinuousLinearMap=fderiv ℝ hillL2NativeMap u :=
  (exists_hillL2NativeMap_derivative_equiv u).choose_spec

theorem isLocalHomeomorph_hillL2NativeMap : IsLocalHomeomorph hillL2NativeMap := by
  exact @NLS.FunctionalAnalysis.isLocalHomeomorph_of_analytic_equiv_fderiv ℝ
    HillRealL2BanachSource HillRealSignedHalfTarget inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    hillL2NativeMap analyticAt_hillL2NativeMap hillL2NativeJacobianEquiv
    (fun u => (hillL2NativeJacobianEquiv_toContinuousLinearMap u).symm)

theorem isOpenMap_hillL2NativeMap : IsOpenMap hillL2NativeMap :=
  isLocalHomeomorph_hillL2NativeMap.isOpenMap

end NLS.Articles.KdVPseudomeasures
