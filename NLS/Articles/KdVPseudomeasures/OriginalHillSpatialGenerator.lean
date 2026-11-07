import NLS.Articles.KdVPseudomeasures.OriginalHillSpatialNormalization
import NLS.KdV.HillRealSpatialGenerator
import NLS.SequenceSpaces.SignedSobolevGeneratorRegularity

/-! Differentiating the ACTUAL original spatial covariance identifies the
full native derivative on the physical generator. It gives full native
positive-half regularity for EVERY original L2 source, without a global
inverse, finite-gap or endpoint-only assumption. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- Full native derivative intertwines the actual spatial generators,
with exact original2*pi*k at EVERY signed coordinate. -/
theorem fderiv_hillRealSignedMap_spatialGenerator (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) (k : ℤ) :
    ((fderiv ℝ hillRealSignedMap q) v).val.val.val k=
      I*((2*Real.pi*k:ℝ):ℂ)*(hillRealSignedMap q).val.val.val k := by
  have hs := hasDerivAt_hillRealSpatialTranslation q v hv 0
  simp only [hillRealSpatialTranslation_zero] at hs
  have hd := @NLS.FunctionalAnalysis.hasDerivAt_differentiable_comp HillRealMeanZeroSource HillRealSignedTarget
    inferInstance inferInstance inferInstance inferInstance hillRealSignedMap
    (fun s => hillRealSpatialTranslation s q) v 0
    (analyticAt_hillRealSignedMap (hillRealSpatialTranslation 0 q)).differentiableAt hs
  simp only [hillRealSpatialTranslation_zero] at hd
  have he := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp HillRealSignedTarget ℂ
    inferInstance inferInstance inferInstance inferInstance
    (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 k) _ _ 0 hd
  change HasDerivAt (fun s => (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val.val k)
    (((fderiv ℝ hillRealSignedMap q) v).val.val.val k) 0 at he
  have hp := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (I*((2*Real.pi*k:ℝ):ℂ)) 0).mul_const
    ((hillRealSignedMap q).val.val.val k)
  have hphase (s : ℝ) : I*((2*Real.pi*k:ℝ):ℂ)*(s:ℂ)=((s*(2*Real.pi*k):ℝ):ℂ)*I := by
    push_cast
    ring
  simp_rw [hphase] at hp
  simp only [zero_mul,ofReal_zero,exp_zero,one_mul] at hp
  have hfun : (fun s => (hillRealSignedMap (hillRealSpatialTranslation s q)).val.val.val k)=
      (fun s => exp (((s*(2*Real.pi*k):ℝ):ℂ)*I)*(hillRealSignedMap q).val.val.val k) :=
    funext (fun s => hillRealSignedMap_spatialTranslation_apply q s k)
  rw [hfun] at he
  exact he.unique hp

/-- The SAME actual native output gains a full signed Sobolev order at
EVERY source in the physical spatial-generator domain. -/
theorem exists_native_signed_half_of_spatialGenerator (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) :
    ∃ z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2,
      (∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k) ∧
      ‖z‖ ≤ (1/(2*Real.pi))*‖(fderiv ℝ hillRealSignedMap q) v‖ := by
  have hx := WeightedCoeff.exists_signedSobolev_succ_of_spatialGenerator (p:=2) (-1/2)
    (hillRealSignedMap q).val.val.val (hillRealSignedMap q).val.property
    ((fderiv ℝ hillRealSignedMap q) v).val.val
    (fderiv_hillRealSignedMap_spatialGenerator q v hv)
  rw [show (-1/2:ℝ)+1=1/2 by norm_num] at hx
  obtain ⟨b,hb,hn⟩ := hx
  have h0 : b.val 0=0 := (hb 0).trans (hillRealSignedMap q).val.property
  have hr (k : ℤ) : b.val (-k)=(starRingEnd ℂ) (b.val k) := by
    rw [hb,hb,(hillRealSignedMap q).property]
  refine ⟨⟨⟨b,h0⟩,hr⟩,hb,?_⟩
  convert hn using 1 <;> rfl

/-- Every original physical L2 source has its ENTIRE actual native output
in literal signed positive-half Hilbert space, with unchanged coefficients
and the original physical real symmetry. -/
theorem exists_native_signed_half_of_L2_source (q : HillRealMeanZeroSource) (u : Coeff 2)
    (hu : ∀ k : ℤ, u k=q.val.val.val k) :
    ∃ z : WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2,
      ∀ k : ℤ, z.val.val.val k=(hillRealSignedMap q).val.val.val k := by
  obtain ⟨v,hv⟩ := exists_hillRealSpatialGenerator_of_L2 q u hu
  obtain ⟨z,hz,_⟩ := exists_native_signed_half_of_spatialGenerator q v hv
  exact ⟨z,hz⟩

end NLS.Articles.KdVPseudomeasures
