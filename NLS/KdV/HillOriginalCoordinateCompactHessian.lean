import NLS.KdV.HillOriginalHminusCompactOperator
import NLS.KdV.HillOriginalCartesianGardnerFamily
import NLS.FunctionalAnalysis.CompactGermSecondDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- Each actual normalized coordinate Hessian is compact as an operator
from the ORIGINAL mean-zero L2 domain into its real complex-valued dual.
The proof uses an actual physical H-minus-one germ, including closed gaps. -/
theorem isCompactOperator_hillOriginalMeanZeroCoordinate_secondDerivative
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    IsCompactOperator (fderiv ℝ (fderiv ℝ
      (fun p : hillRealMeanZeroSourceSubmodule => hillOriginalMeanZeroRealSpectralMap p k)) q) := by
  let Q : RealPeriodOneHillPotential := ⟨q.val.val,q.val.property⟩
  let n : ℕ+ := ⟨k+1,by omega⟩
  obtain ⟨G,hG,hGM⟩ := exists_hillOriginal_signedCartesian_hminus_physical_germ_all_gaps Q n true
  let L := hillOriginalRealHminusInclusion.comp hillRealMeanZeroSourceSubmodule.subtypeL
  let C : ℂ := Real.sqrt (2*Real.pi*(k+1 : ℕ))
  let F : PeriodOneHminusOne → ℂ := fun p => C*G p
  have hF : AnalyticAt ℝ F (L q) :=
    (analyticAt_const.mul hG).restrictScalars (𝕜 := ℝ)
  have hQ : Continuous (fun p : hillRealMeanZeroSourceSubmodule =>
      (⟨p.val.val,p.val.property⟩ : RealPeriodOneHillPotential)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : (fun p : hillRealMeanZeroSourceSubmodule => hillOriginalMeanZeroRealSpectralMap p k) =ᶠ[𝓝 q]
      (fun p => F (L p)) := by
    filter_upwards [hQ.continuousAt.tendsto.eventually hGM] with p hp
    change hillOriginalBaseSpectralSequence (⟨p.val.val,p.val.property⟩ : RealPeriodOneHillPotential) k = _
    rw [hillOriginalBaseSpectralSequence_apply,←hp]
    rfl
  exact NLS.FunctionalAnalysis.isCompactOperator_fderiv_fderiv_of_compact_germ L
    isCompactOperator_hillOriginalMeanZeroHminusInclusion F q hF _ he

end NLS.KdV
