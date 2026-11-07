import NLS.FunctionalAnalysis.CompactInvariantGlobalCurve

/-! The complete actual integral curve is continuous in the original
Banach norm at every time, directly from its proved strong derivative. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : Type*}
namespace CompactInvariantVectorField

theorem continuous_globalCurve (D : CompactInvariantVectorField E S) (q : E) :
    Continuous (D.globalCurve q) :=
  continuous_iff_continuousAt.mpr (fun t => (D.hasDerivAt_globalCurve q t).continuousAt)

end CompactInvariantVectorField
end NLS.FunctionalAnalysis
