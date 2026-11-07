import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! A norm bound for a linear term and two stronger remainders, with
opaque original Banach spaces and unchanged checking limits. -/
namespace NLS.FunctionalAnalysis

theorem norm_clm_add_sub_le {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) (a : E) (b c : F) :
    ‖L a+b-c‖≤‖L‖*‖a‖+‖b‖+‖c‖ := by
  calc
    ‖L a+b-c‖≤‖L a+b‖+‖c‖ := norm_sub_le _ _
    _≤(‖L a‖+‖b‖)+‖c‖ := add_le_add (norm_add_le _ _) le_rfl
    _≤(‖L‖*‖a‖+‖b‖)+‖c‖ := add_le_add (add_le_add (L.le_opNorm a) le_rfl) le_rfl

end NLS.FunctionalAnalysis
