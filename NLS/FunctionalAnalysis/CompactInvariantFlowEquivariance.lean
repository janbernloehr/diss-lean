import NLS.FunctionalAnalysis.CompactInvariantGlobalCurve

/-! A bounded linear symmetry of the actual vector field commutes with its
complete constructed flow, by genuine C1 integral-curve uniqueness. -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : Type*}
namespace CompactInvariantVectorField

/-- Every bounded real-linear field symmetry commutes with the complete
flow at EVERY real time, with no separate flow-equivariance premise. -/
theorem globalCurve_equivariant (D : CompactInvariantVectorField E S) (T : E →L[ℝ] E)
    (hT : ∀ q : E, T (D.field q)=D.field (T q)) (q : E) (t : ℝ) :
    D.globalCurve (T q) t=T (D.globalCurve q t) := by
  have hd (s : ℝ) : HasDerivAt (fun u => T (D.globalCurve q u))
      (D.field (T (D.globalCurve q s))) s := by
    simpa only [hT,Function.comp_def] using T.hasFDerivAt.comp_hasDerivAt s (D.hasDerivAt_globalCurve q s)
  have he := eqOn_integralCurves_of_contDiffAt D.field (fun u => T (D.globalCurve q u))
    (D.globalCurve (T q)) univ isOpen_univ isPreconnected_univ (fun s _ => hd s)
    (fun s _ => D.hasDerivAt_globalCurve (T q) s) (fun _ _ => D.contDiff.contDiffAt)
    0 (mem_univ _) (by rw [D.globalCurve_zero,D.globalCurve_zero])
  exact (he (mem_univ t)).symm

end CompactInvariantVectorField
end NLS.FunctionalAnalysis
