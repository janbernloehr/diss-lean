import NLS.Articles.KdVPseudomeasures.OriginalHillSpatialGenerator
import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator
import NLS.KdV.HillRealSpatialGeneratorL2
import NLS.FunctionalAnalysis.NormedLinearBound

/-! EXACT L2/source and signed positive-half/output regularity for the
ACTUAL native map. Strong spatial differentiation passes through the
proved analytic local inverse. Neither global injectivity nor global
surjectivity nor an inverse-regularity premise is assumed. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- A native positive-half output supplies the original source spatial
generator through the ACTUAL analytic local inverse, with its full norm
controlled by the actual inverse Jacobian and the actual output norm. -/
theorem exists_source_spatialGenerator_of_native_signed_half (q : HillRealMeanZeroSource)
    (z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2)
    (hz : ∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k) :
    ∃ v : HillRealMeanZeroSource,
      (∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) ∧
      ‖v‖ ≤ (2*Real.pi)*‖(hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap‖*‖z‖ := by
  obtain ⟨δ,hδ,hδnorm⟩ := WeightedCoeff.exists_fourierRealZeroSignedSpatialGenerator
    (p:=2) (-1/2) (1/2) (by norm_num) z
  have hvδ (k : ℤ) : δ.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*(hillRealSignedMap q).val.val.val k := by
    rw [hδ,hz]
  let γ : ℝ → HillRealMeanZeroSource := fun t => hillRealSpatialTranslation t q
  let Z : ℝ → HillRealSignedTarget := fun t => hillRealSignedMap (γ t)
  have hZ : HasDerivAt Z δ 0 :=
    WeightedCoeff.hasDerivAt_fourierRealZero_spatialCurve (Weight.signedSobolev (-1/2))
      (Weight.signedSobolev_neg (-1/2)) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      (hillRealSignedMap q) δ hvδ Z (fun t k => hillRealSignedMap_spatialTranslation_apply q t k)
  obtain ⟨g,hga,_,hleft,_,hgd⟩ := hillPhysicalNativeMap_localInverse q
  let v : HillRealMeanZeroSource := (hillPhysicalNativeJacobianEquiv q).symm δ
  have hgZ : DifferentiableAt ℝ g (Z 0) := by
    simpa only [Z,γ,hillRealSpatialTranslation_zero] using hga.differentiableAt
  have hd := @NLS.FunctionalAnalysis.hasDerivAt_differentiable_comp HillRealSignedTarget HillRealMeanZeroSource
    inferInstance inferInstance inferInstance inferInstance g Z δ 0 hgZ hZ
  simp only [Z,γ,hillRealSpatialTranslation_zero] at hd
  rw [hgd] at hd
  change HasDerivAt (fun t => g (hillRealSignedMap (γ t))) v 0 at hd
  have hcont : Tendsto γ (𝓝 (0:ℝ)) (𝓝 q) := by
    simpa only [γ,hillRealSpatialTranslation_zero] using
      ((continuous_hillRealSpatialTranslation_orbit q).continuousAt (x:=0)).tendsto
  have heq : (fun t => g (hillRealSignedMap (γ t))) =ᶠ[𝓝 (0:ℝ)] γ := hcont.eventually hleft
  have hsource : HasDerivAt γ v 0 := heq.hasDerivAt_iff.mp hd
  have hγ (t : ℝ) (k : ℤ) : (γ t).val.val.val k=
      exp (((t*(2*Real.pi*k):ℝ):ℂ)*I)*q.val.val.val k := by
    change (hillRealMeanZeroInclusion (hillRealSpatialTranslation t q)).val k= _
    rw [hillRealSpatialTranslation_inclusion,WeightedCoeff.spatialTranslation_apply]
    rfl
  refine ⟨v,WeightedCoeff.fourierRealZero_spatialGenerator_of_hasDerivAt
    (Weight.sobolev (-1)) q v γ hγ hsource,?_⟩
  have hnorm := @NLS.FunctionalAnalysis.norm_clm_apply_le_of_norm_le ℝ HillRealSignedTarget HillRealMeanZeroSource
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap δ ((2*Real.pi)*‖z‖) hδnorm
  calc
    ‖v‖ ≤ ‖(hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap‖*((2*Real.pi)*‖z‖) := hnorm
    _ = _ := by ring

/-- ANY actual native positive-half output has its SAME ENTIRE original
source coefficients in L2. The proof needs no global native inverse. -/
theorem exists_L2_source_of_native_signed_half (q : HillRealMeanZeroSource)
    (z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2)
    (hz : ∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k) :
    ∃ u : Coeff 2, ∀ k : ℤ, u k=q.val.val.val k := by
  obtain ⟨v,hv,_⟩ := exists_source_spatialGenerator_of_native_signed_half q z hz
  exact exists_L2_of_hillRealSpatialGenerator q v hv

/-- EXACT original L2/source and native signed positive-half/output
regularity equivalence on the full original physical source. -/
theorem hillReal_source_L2_iff_native_signed_half (q : HillRealMeanZeroSource) :
    (∃ u : Coeff 2, ∀ k : ℤ, u k=q.val.val.val k) ↔
      ∃ z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2,
        ∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k := by
  constructor
  · rintro ⟨u,hu⟩
    exact exists_native_signed_half_of_L2_source q u hu
  · rintro ⟨z,hz⟩
    exact exists_L2_source_of_native_signed_half q z hz

/-- The exact equivalence on the ENTIRE original distribution source,
retaining the same original coefficients and the same actual native map. -/
theorem original_Hill_L2_iff_native_signed_half (q : OriginalHminusOnePotential) :
    (∃ u : Coeff 2, ∀ k : ℤ, u k=(originalPeriodOneCoefficients q).val k) ↔
      ∃ z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2,
        ∀ k : ℤ, z.val.val.val k=hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := by
  let Q := originalHillRealMeanZeroSource q
  have hs (k : ℤ) : Q.val.val.val k=(originalPeriodOneCoefficients q).val k :=
    congrArg (fun a : PeriodOneHminusOne => a.val k) (originalHillRealMeanZeroSource_inclusion q)
  have ht (k : ℤ) : (hillRealSignedMap Q).val.val.val k=
      hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := by
    rw [hillRealSignedMap_coordinate,originalHillRealMeanZeroSource_inclusion]
  simpa only [hs,ht] using hillReal_source_L2_iff_native_signed_half Q

end NLS.Articles.KdVPseudomeasures
