import NLS.Articles.KdVPseudomeasures.OriginalEndpointRealCoordinates

/-! The coefficient Banach model has EXACTLY the original physical
endpoint norm topology. Both directions are restrictions of bounded
linear ambient maps; all original distributions are retained. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The subspace topology from the ORIGINAL Fourier-Lebesgue norm. -/
instance potentialNormTopology (r : ℝ) : TopologicalSpace (Potential r) :=
  inferInstanceAs (TopologicalSpace {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ // q.val.IsRealMeanZeroPeriodOne})

theorem originalEndpointPotential_zero_val (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (originalEndpointPotential r hr 0).val=0 := by
  change periodOneEndpointOriginal r hr.1 0=0
  exact map_zero _

theorem originalEndpointRealSource_potential (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    originalEndpointRealSource r hr (originalEndpointPotential r hr q)=q :=
  (originalEndpointRealSourceEquiv r hr).apply_symm_apply q

theorem originalEndpointPotential_source (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    originalEndpointPotential r hr (originalEndpointRealSource r hr q)=q :=
  (originalEndpointRealSourceEquiv r hr).symm_apply_apply q

theorem continuous_originalEndpointRealSource (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Continuous (originalEndpointRealSource r hr) := by
  have hraw : Continuous (fun q : Potential r => periodOneEndpointExtract r hr.1 q.val) :=
    (periodOneEndpointExtract r hr.1).continuous.comp continuous_subtype_val
  have hzero : Continuous (fun q : Potential r => (originalEndpointRealSource r hr q).val) :=
    hraw.subtype_mk _
  exact hzero.subtype_mk _

theorem continuous_originalEndpointPotential (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Continuous (originalEndpointPotential r hr) := by
  have hraw : Continuous (fun q : HillEndpointRealMeanZeroSource r =>
      periodOneEndpointOriginal r hr.1 q.val.val) :=
    (periodOneEndpointOriginal r hr.1).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact hraw.subtype_mk _

def originalEndpointRealSourceHomeomorph (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Potential r ≃ₜ HillEndpointRealMeanZeroSource r where
  toEquiv := originalEndpointRealSourceEquiv r hr
  continuous_toFun := continuous_originalEndpointRealSource r hr
  continuous_invFun := continuous_originalEndpointPotential r hr

def originalEndpointRealInclusionCLM (r : ℝ) (hr : AdmissiblePredualOrder r) :
    HillEndpointRealMeanZeroSource r →L[ℝ] FourierLebesgueSpace (2:ℝ) (-r) ⊤ :=
  ((periodOneEndpointOriginal r hr.1).restrictScalars ℝ).comp
    ((((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-r)) ⊤).subtypeL).restrictScalars ℝ).comp
      (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-r)) ⊤).subtypeL)

theorem originalEndpointRealInclusionCLM_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) :
    originalEndpointRealInclusionCLM r hr q=(originalEndpointPotential r hr q).val := rfl

theorem continuous_originalEndpointRealSignedCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Continuous (originalEndpointRealSignedCoordinates r hr) :=
  (continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillEndpointRealSignedMap r hr q).continuousAt)).comp
    (continuous_originalEndpointRealSource r hr)

end NLS.Articles.KdVPseudomeasures
