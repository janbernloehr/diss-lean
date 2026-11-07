import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Pull an analytic Banach-valued map through a bounded linear source
inclusion on the exact preimage domain, without expanding source norms. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem analyticOnNhd_clm_preimage
    {𝕜 E Q Y : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (L : E →L[𝕜] Q) (A : Q → Y) (U : Set Q) (hA : AnalyticOnNhd 𝕜 A U) :
    AnalyticOnNhd 𝕜 (fun p => A (L p)) (L ⁻¹' U) :=
  fun p hp => (hA (L p) hp).comp (L.analyticAt p)

end NLS.ComplexAnalysis
