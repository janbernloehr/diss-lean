import NLS.Articles.KdVKdV2Frequencies.GlobalRoughRealInverse
import NLS.SequenceSpaces.PhysicalRealSobolevInclusion

/-! # The SAME actual global forward map at EVERY native Sobolev order

The global native map is the literal raw signed output of the already-fixed
rough map. The proved nonlinear Sobolev criterion supplies its native norm.
The exact inclusion diagram identifies all its analytic germs; no separate
forward map is chosen at any order or source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Literal native real mean-zero source in the ORIGINAL rough space. -/
def realNativeSource (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) : PeriodOneHminusOne :=
  periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a.val)

theorem realNativeSource_real (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    IsRealPeriodOneHminusOne (realNativeSource t ht a) := by
  have h := (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (t-1)) a.val).mpr a.property
  intro j
  simpa only [realNativeSource,periodOneSobolevImageInclusion_apply] using h j

theorem realNativeSource_zero (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    (realNativeSource t ht a).val 0=0 := by
  simp only [realNativeSource,periodOneSobolevImageInclusion_apply,WeightedCoeff.meanZeroWeightedLift_zero]

theorem realNativeSource_weak_lift (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    realNativeSource t ht a=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
      (physicalRealSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a).val :=
  (WeightedCoeff.meanZeroSobolevInclusion_lift (by linarith : (-1 : ℝ)≤t-1) a.val).symm

theorem realNativeSource_mem (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    Memℓp (fun j => (Weight.sobolev (t-1) j : ℂ)*(realNativeSource t ht a).val j) 2 := by
  simp only [realNativeSource,periodOneSobolevImageInclusion_apply]
  exact (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a.val).property

/-- The literal SAME raw output now in its exact native target space. -/
def realNativeTarget (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) : WeightedCoeff (Weight.sobolev (t-1/2)) 2 :=
  ⟨(D.signed (realNativeSource t ht a)).val,by
    change Memℓp (fun j => (Weight.sobolev (t-1/2) j : ℂ)*(D.signed (realNativeSource t ht a)).val j) 2
    have h := (D.sobolev_iff_signed_mem _ (realNativeSource_real t ht a) (t-1) (by linarith)).mp
      (realNativeSource_mem t ht a)
    simpa only [show t-1+1/2=t-1/2 by ring] using h⟩

theorem realNativeTarget_inclusion (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) :
    WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (D.realNativeTarget t ht a)=
      D.signed (realNativeSource t ht a) := by
  apply Subtype.ext
  funext j
  exact WeightedCoeff.sobolevInclusion_apply _ _ j

theorem realNativeTarget_zero (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) : (D.realNativeTarget t ht a).val 0=0 :=
  D.signed_zero _ (D.real_mem_domain _ (realNativeSource_real t ht a))

/-- Global native restriction of the SAME signed actual forward map,
normalized with the literal source order t-1 and target order t-1/2. -/
def realNativeForward (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    physicalRealDeletedSubmodule → physicalRealDeletedSubmodule := fun a =>
  ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2)) (D.realNativeTarget t ht a),
    meanZeroWeightedProjection_real _ (Weight.sobolev_neg (t-1/2)) _
      (D.signed_real _ (realNativeSource_real t ht a))⟩

/-- Exact global commuting diagram, not only a local real agreement. -/
theorem realNativeForward_weak_commuting (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    physicalRealSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (D.realNativeForward t ht a)=
      D.realWeakForward (physicalRealSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a) := by
  apply Subtype.ext
  change WeightedCoeff.meanZeroSobolevInclusion _
    (WeightedCoeff.meanZeroWeightedProjectionCLM _ (D.realNativeTarget t ht a))=_
  rw [WeightedCoeff.meanZeroSobolevInclusion_projection,D.realNativeTarget_inclusion]
  rw [realNativeSource_weak_lift]
  rfl

/-- Full literal native target recovery, including the central slot. -/
theorem realNativeForward_target_lift (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0≤t) (a : physicalRealDeletedSubmodule) :
    WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) (D.realNativeForward t ht a).val=
      D.realNativeTarget t ht a :=
  WeightedCoeff.meanZeroWeightedLift_projection _ _ (D.realNativeTarget_zero t ht a)

/-- The actual global forward restriction is real analytic at EVERY
native Sobolev order, in its literal native source AND target norms. -/
theorem realNativeForward_analytic (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) :
    AnalyticOnNhd ℝ (D.realNativeForward t ht) univ := by
  intro a _
  obtain ⟨V,_hV,_haV,g,_hga,hcomm,P,_hP,haP,hPV,hFa,_hPia,_hleft,_hright⟩ :=
    D.exists_native_analytic_inverse_at t ht a.val (realNativeSource_real t ht a)
  have he (b : physicalRealDeletedSubmodule) (hb : b.val∈P.source) :
      nativeMeanZeroAbelianMap t g b.val=(D.realNativeForward t ht b).val := by
    apply WeightedCoeff.meanZeroSobolevInclusion_injective (by linarith : (-1/2 : ℝ)≤t-1/2)
    have h := nativeMeanZeroAbelianMap_commuting t ht D.signed g b.val
      (hcomm _ (hPV hb)).2.1
    exact h.trans (congrArg Subtype.val (D.realNativeForward_weak_commuting t ht b)).symm
  apply (analyticAt_physicalRealDeletedRestriction (hFa a.val haP)).congr
  filter_upwards [(P.open_source.preimage continuous_subtype_val).mem_nhds haP] with b hb
  change physicalRealDeletedProjection (nativeMeanZeroAbelianMap t g b.val)=D.realNativeForward t ht b
  rw [he b hb]
  exact physicalRealDeletedProjection_coe _

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
