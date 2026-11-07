import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Linear scalar observations identify the ENTIRE actual derivative
of a native Banach-valued core on its original open neighborhood. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem eq_derivative_of_linear_observations
    {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (U : Set E) (hU : IsOpen U) (h0 : (0:E)∈U)
    (A : E → F) (DA : E →L[𝕜] F) (hAd : HasFDerivAt A DA 0)
    (obs : ι → F →L[𝕜] 𝕜)
    (hsep : ∀ x y : F,(∀ i,obs i x=obs i y) → x=y)
    (hc : ∀ i,∃ C : E →L[𝕜] 𝕜,∀ q∈U,obs i (A q)=C q) :
    ∀ q∈U,A q=DA q := by
  intro q hq
  apply hsep
  intro i
  obtain ⟨C,hC⟩ := hc i
  have he : (fun p => obs i (A p))=ᶠ[𝓝 (0:E)]C := by
    filter_upwards [hU.mem_nhds h0] with p hp
    exact hC p hp
  have hd : (obs i).comp DA=C :=
    (((obs i).hasFDerivAt.comp 0 hAd).congr_of_eventuallyEq he.symm).unique C.hasFDerivAt
  exact (hC q hq).trans (congrArg (fun T : E →L[𝕜] 𝕜 => T q) hd).symm

end NLS.ComplexAnalysis
