import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Removing the ACTUAL derivative of the stronger remainder aligns an
exact analytic decomposition with the SAME map's true linearization. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_analytic_remainder_at_true_linearization
    {𝕜 E F H Q : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
    (U : Set E) (hU : IsOpen U) (h0 : (0:E)∈U)
    (A : E → F) (R : E → H) (Y : E → Q) (I : F →L[𝕜] Q) (J : H →L[𝕜] Q)
    (DA : E →L[𝕜] F) (DR : E →L[𝕜] H) (M : E →L[𝕜] Q)
    (hAd : HasFDerivAt A DA 0) (hRd : HasFDerivAt R DR 0) (hYd : HasFDerivAt Y M 0)
    (hRa : AnalyticOnNhd 𝕜 R U) (hAe : ∀ q∈U,A q=DA q)
    (hY : ∀ q∈U,Y q=I (A q)+J (R q)) :
    ∃ S : E → H,AnalyticOnNhd 𝕜 S U ∧ ∀ q∈U,Y q=M q+J (S q) := by
  have he : (fun q => I (A q)+J (R q))=ᶠ[𝓝 (0:E)]Y := by
    filter_upwards [hU.mem_nhds h0] with q hq
    exact (hY q hq).symm
  have hd : I.comp DA+J.comp DR=M :=
    ((((I.hasFDerivAt.comp 0 hAd).add (J.hasFDerivAt.comp 0 hRd)).congr_of_eventuallyEq he.symm)).unique hYd
  refine ⟨(fun q => R q-DR q),hRa.sub (fun q _ => DR.analyticAt q),?_⟩
  intro q hq
  rw [hY q hq,hAe q hq,←hd]
  simp only [add_apply,ContinuousLinearMap.comp_apply,map_sub]
  abel

end NLS.ComplexAnalysis
