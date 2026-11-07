import NLS.KdV.HillActionSpatialTranslation

/-! Joint continuity of the literal physical real mean-zero source
translation, in the original Hminus-one Banach topology. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem continuous_hillRealSpatialTranslation :
    Continuous (fun x : ℝ × HillRealMeanZeroSource => hillRealSpatialTranslation x.1 x.2) := by
  have hI : Continuous (fun x : ℝ × HillRealMeanZeroSource =>
      (x.1,hillRealMeanZeroInclusion x.2)) :=
    continuous_fst.prodMk (hillRealMeanZeroInclusion.continuous.comp continuous_snd)
  have hW := WeightedCoeff.continuous_spatialTranslation (p:=2) (Weight.sobolev (-1))
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (2*Real.pi)
  have hT := hW.comp hI
  change Continuous (fun x : ℝ × HillRealMeanZeroSource => hillRealMeanZeroProjection
    (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) x.1
      (hillRealMeanZeroInclusion x.2)))
  convert hillRealMeanZeroProjection.continuous.comp hT using 1
  rfl


/-- Every physical source has a continuous spatial orbit in Hminus-one. -/
theorem continuous_hillRealSpatialTranslation_orbit (q : HillRealMeanZeroSource) :
    Continuous (fun t : ℝ => hillRealSpatialTranslation t q) := by
  have hp : Continuous (fun t : ℝ => (t,q)) := continuous_id.prodMk continuous_const
  convert continuous_hillRealSpatialTranslation.comp hp using 1
  rfl

end NLS.KdV
