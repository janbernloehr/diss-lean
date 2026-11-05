import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.KdV.HillActionHamiltonianField
import NLS.FunctionalAnalysis.CompactInvariantGlobalCurve

/-! The ACTUAL indexed action Hamiltonian fields are complete, because
their entire actual discriminant fibers are compact in Hminus-one norm. -/
noncomputable section
open Set NLS.KdV NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

def originalHillActionHamiltonianSystem (n : ℕ+) :
    CompactInvariantVectorField HillRealMeanZeroSource (ℂ → ℂ) where
  field := hillRealActionHamiltonianVector n
  contDiff := contDiff_hillRealActionHamiltonianVector n
  invariant := hillRealDiscriminantData
  compact_fiber := isCompact_hillRealDiscriminant_fiber
  conserved := hillRealDiscriminantData_eq_on_action_integralCurve n

/-- Complete flow of the actual canonical action with its original normalization. -/
def originalHillNativeActionFlow (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) : HillRealMeanZeroSource :=
  (originalHillActionHamiltonianSystem n).globalCurve q t

theorem originalHillNativeActionFlow_zero (n : ℕ+) (q : HillRealMeanZeroSource) :
    originalHillNativeActionFlow n q 0=q :=
  (originalHillActionHamiltonianSystem n).globalCurve_zero q

theorem hasDerivAt_originalHillNativeActionFlow (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    HasDerivAt (originalHillNativeActionFlow n q)
      (hillRealActionHamiltonianVector n (originalHillNativeActionFlow n q t)) t :=
  (originalHillActionHamiltonianSystem n).hasDerivAt_globalCurve q t

theorem originalHillNativeActionFlow_add (n : ℕ+) (q : HillRealMeanZeroSource) (s t : ℝ) :
    originalHillNativeActionFlow n q (t+s)=
      originalHillNativeActionFlow n (originalHillNativeActionFlow n q s) t :=
  (originalHillActionHamiltonianSystem n).globalCurve_add q s t

theorem originalHillNativeActionFlow_conserved (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    hillRealDiscriminantData (originalHillNativeActionFlow n q t)=hillRealDiscriminantData q :=
  (originalHillActionHamiltonianSystem n).globalCurve_conserved q t

theorem hasDerivAt_originalHillNativeActionFlow_inclusion (n : ℕ+) (q : HillRealMeanZeroSource) (t : ℝ) :
    HasDerivAt (fun τ => hillRealMeanZeroInclusion (originalHillNativeActionFlow n q τ))
      (hillHminusActionHamiltonianVector n
        (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t))) t := by
  simpa only [hillRealActionHamiltonianVector_inclusion] using
    hasDerivAt_hillRealMeanZeroInclusion_comp _ _ t (hasDerivAt_originalHillNativeActionFlow n q t)

end NLS.Articles.KdVPseudomeasures
