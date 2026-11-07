import NLS.KdV.HillRealSpatialTranslationContinuity
import NLS.FunctionalAnalysis.LinearCurveDerivative
import NLS.SequenceSpaces.PeriodOneMiuraSpatialTranslation

/-! Strong spatial differentiation on the actual physical mean-zero source.
Every literal L2 input supplies its original distributional generator. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.KdV

/-- Generator-domain differentiation in the original physical Hminus norm. -/
theorem hasDerivAt_hillRealSpatialTranslation (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) (t : ℝ) :
    HasDerivAt (fun s => hillRealSpatialTranslation s q) (hillRealSpatialTranslation t v) t := by
  have hd := WeightedCoeff.hasDerivAt_spatialTranslation (p:=2) (Weight.sobolev (-1))
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (2*Real.pi)
    (hillRealMeanZeroInclusion q) (hillRealMeanZeroInclusion v) hv t
  have hp := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp PeriodOneHminusOne HillRealMeanZeroSource
    inferInstance inferInstance inferInstance inferInstance hillRealMeanZeroProjection _ _ t hd
  change HasDerivAt (fun s => hillRealSpatialTranslation s q) (hillRealSpatialTranslation t v) t at hp
  exact hp

/-- Every source whose ENTIRE literal coefficient sequence is L2 has its
physical spatial generator in the SAME mean-zero real Hminus source. -/
theorem exists_hillRealSpatialGenerator_of_L2 (q : HillRealMeanZeroSource) (u : Coeff 2)
    (hu : ∀ k : ℤ, u k=q.val.val.val k) :
    ∃ v : HillRealMeanZeroSource, ∀ k : ℤ,
      v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k := by
  let d := periodOneL2SpatialDerivative u
  have hd (k : ℤ) : d.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k := by
    rw [periodOneL2SpatialDerivative_apply,hu]
    push_cast
    ring
  have hr (k : ℤ) : d.val (-k)=(starRingEnd ℂ) (d.val k) := by
    rw [hd,hd,q.property,map_mul,map_mul]
    simp only [Int.cast_neg,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  have h0 : d.val 0=0 := by rw [hd]; simp
  let v := hillRealMeanZeroProjection d
  have hi : hillRealMeanZeroInclusion v=d := hillRealMeanZeroProjection_inclusion d hr h0
  refine ⟨v,fun k => ?_⟩
  change (hillRealMeanZeroInclusion v).val k= _
  rw [hi,hd]

end NLS.KdV
