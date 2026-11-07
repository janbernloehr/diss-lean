import NLS.Articles.KdVPseudomeasures.OriginalHillNativeL2Regularity
import NLS.KdV.HillNativeL2Models
import NLS.FunctionalAnalysis.AnalyticGeneratorRecovery

/-! The ACTUAL native map on the genuine L2 and signed positive-half
Banach models is FULLY real analytic. Bounded generator recovery applied
to the actual full native derivative gives an explicit formula, with no
coordinatewise real-analytic assembly or global inverse assumption. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- Actual native map in the stronger Banach norms, recovered explicitly
from its actual native derivative and the original spatial generator. -/
def hillL2NativeMap (u : HillRealL2BanachSource) : HillRealSignedHalfTarget :=
  hillSignedHalfSpatialRecovery
    ((fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)) (hillL2SourceSpatialGenerator u))

/-- The recovered map is the SAME ENTIRE actual native output. -/
theorem hillL2NativeMap_inclusion (u : HillRealL2BanachSource) :
    hillSignedHalfInclusion (hillL2NativeMap u)=hillRealSignedMap (hillL2SourceInclusion u) := by
  apply hillSignedHalfInclusion_recovery_eq
  apply fderiv_hillRealSignedMap_spatialGenerator
  intro k
  rw [hillL2SourceSpatialGenerator_apply,hillL2SourceInclusion_apply]

theorem hillL2NativeMap_apply (u : HillRealL2BanachSource) (k : ℤ) :
    (hillL2NativeMap u).val.val.val k=(hillRealSignedMap (hillL2SourceInclusion u)).val.val.val k := by
  have h := congrArg (fun z : HillRealSignedTarget => z.val.val.val k) (hillL2NativeMap_inclusion u)
  simpa only [hillSignedHalfInclusion_apply] using h

/-- FULL real Banach-space analyticity in the TRUE L2 source and native
positive-half target norms, through bounded generator recovery. -/
theorem analyticAt_hillL2NativeMap (u : HillRealL2BanachSource) : AnalyticAt ℝ hillL2NativeMap u := by
  exact @NLS.FunctionalAnalysis.analyticAt_derivative_generator_recovery ℝ
    HillRealMeanZeroSource HillRealSignedTarget HillRealL2BanachSource HillRealSignedHalfTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hillRealSignedMap
    hillL2SourceInclusion hillL2SourceSpatialGenerator hillSignedHalfSpatialRecovery u
    (analyticAt_hillRealSignedMap (hillL2SourceInclusion u))

/-- Pointwise actual L2-to-positive-half norm control by the ACTUAL native
Jacobian norm; the physical2*pi generator constants cancel exactly. -/
theorem norm_hillL2NativeMap_le_DF (u : HillRealL2BanachSource) :
    ‖hillL2NativeMap u‖ ≤ ‖fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)‖*‖u‖ := by
  have hd := @NLS.FunctionalAnalysis.norm_clm_apply_le_of_norm_le ℝ HillRealMeanZeroSource HillRealSignedTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)) (hillL2SourceSpatialGenerator u)
    ((2*Real.pi)*‖u‖) (norm_hillL2SourceSpatialGenerator_le u)
  calc
    ‖hillL2NativeMap u‖ ≤ (1/(2*Real.pi))*
        ‖(fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)) (hillL2SourceSpatialGenerator u)‖ :=
      norm_hillSignedHalfSpatialRecovery_le _
    _ ≤ (1/(2*Real.pi))*(‖fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)‖*((2*Real.pi)*‖u‖)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by field_simp

theorem hillL2NativeMap_zero : hillL2NativeMap 0=0 := by
  apply hillSignedHalfInclusion_injective
  rw [hillL2NativeMap_inclusion,map_zero,hillRealSignedMap_zero,map_zero]

/-- The full stronger target spatial generator is the ACTUAL native
Jacobian applied to the original L2 source spatial generator. -/
theorem hillL2NativeMap_spatialGenerator (u : HillRealL2BanachSource) :
    hillSignedHalfSpatialGenerator (hillL2NativeMap u)=
      (fderiv ℝ hillRealSignedMap (hillL2SourceInclusion u)) (hillL2SourceSpatialGenerator u) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillSignedHalfSpatialGenerator_apply,hillL2NativeMap_apply]
  symm
  apply fderiv_hillRealSignedMap_spatialGenerator
  intro j
  rw [hillL2SourceSpatialGenerator_apply,hillL2SourceInclusion_apply]

/-- Quantitative inverse L2 regularity for ANY actual native preimage:
the original L2 norm is bounded by twice the ACTUAL inverse-Jacobian norm
at that source times its actual positive-half output norm. -/
theorem exists_L2_source_of_native_signed_half_norm_bound (q : HillRealMeanZeroSource)
    (z : HillRealSignedHalfTarget)
    (hz : ∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k) :
    ∃ u : Coeff 2, (∀ k : ℤ, u k=q.val.val.val k) ∧
      ‖u‖ ≤ 2*‖(hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap‖*‖z‖ := by
  obtain ⟨v,hv,hn⟩ := exists_source_spatialGenerator_of_native_signed_half q z hz
  let u := hillL2SourceSpatialRecovery v
  have hu := hillL2SourceInclusion_recovery_eq q v hv
  refine ⟨hillL2SourceCoefficients u,?_,?_⟩
  · intro k
    rw [hillL2SourceCoefficients_apply]
    have h := congrArg (fun a : HillRealMeanZeroSource => a.val.val.val k) hu
    simpa only [hillL2SourceInclusion_apply,u] using h
  · rw [norm_hillL2SourceCoefficients]
    calc
      ‖u‖ ≤ (1/Real.pi)*‖v‖ := norm_hillL2SourceSpatialRecovery_le v
      _ ≤ (1/Real.pi)*((2*Real.pi)*‖(hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap‖*‖z‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by field_simp

end NLS.Articles.KdVPseudomeasures
