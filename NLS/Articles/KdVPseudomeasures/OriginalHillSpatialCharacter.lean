import NLS.Articles.KdVPseudomeasures.OriginalHillActionInvariantTopology
import NLS.Articles.KdVPseudomeasures.OriginalHillActionSpatialCommutation
import NLS.KdV.HillRealSpatialTranslationContinuity

/-! The actual open native coordinate has a continuous unimodular spatial
character with physical period one. The specific winding number is NOT
assumed or concluded here. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- The literal actual native spatial quotient at a positive coordinate. -/
def hillRealSpatialCoordinateRatio (n : ℕ+) (s : ℝ) (q : HillRealMeanZeroSource) : ℂ :=
  hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion (hillRealSpatialTranslation s q))/
    hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q)

/-- A native coordinate open at q stays open on its FULL original isoset. -/
theorem hillNativeCoordinate_ne_zero_on_isoset (n : ℕ+) (q p : HillRealMeanZeroSource)
    (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0)
    (hp : hillRealDiscriminantData p=hillRealDiscriminantData q) :
    hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion p) ≠ 0 := by
  have hn := norm_actionTorus_positive q (hillRealSignedMap p)
    (hillRealSignedMap_mem_actionTorus_of_discriminant_eq p q hp) n
  rw [hillRealSignedMap_coordinate,hillRealSignedMap_coordinate] at hn
  intro hzero
  rw [hzero,norm_zero] at hn
  exact hq (norm_eq_zero.mp hn)

theorem continuousOn_hillRealSpatialCoordinateRatio_on_isoset (n : ℕ+) (s : ℝ)
    (q : HillRealMeanZeroSource)
    (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) :
    ContinuousOn (hillRealSpatialCoordinateRatio n s)
      {p | hillRealDiscriminantData p=hillRealDiscriminantData q} := by
  have hc := continuous_hillRealNativeCoordinate (n:ℤ)
  exact (hc.comp (hillRealSpatialTranslation s).continuous).continuousOn.div hc.continuousOn
    (fun p hp => hillNativeCoordinate_ne_zero_on_isoset n q p hq hp)

/-- Actual spatial quotients are locally constant relative to the original
isospectral fiber. No global connectedness or native injectivity is used. -/
theorem exists_open_hillRealSpatialCoordinateRatio_eq_on_isoset (n : ℕ+) (s : ℝ)
    (q : HillRealMeanZeroSource)
    (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) :
    ∃ U : Set HillRealMeanZeroSource, IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, hillRealDiscriminantData p=hillRealDiscriminantData q →
        hillRealSpatialCoordinateRatio n s p=hillRealSpatialCoordinateRatio n s q := by
  exact exists_open_action_invariant_locally_constant_on_isoset q _
    (continuousOn_hillRealSpatialCoordinateRatio_on_isoset n s q hq)
    (fun j p _ t => originalHill_spatialCoordinateRatio_actionFlow_invariant j p s t (n:ℤ))

/-- The actual full discriminant is constant along the physical spatial orbit. -/
theorem hillRealDiscriminantData_spatialTranslation (q : HillRealMeanZeroSource) (t : ℝ) :
    hillRealDiscriminantData (hillRealSpatialTranslation t q)=hillRealDiscriminantData q := by
  funext E
  change hillHminusDiscriminant (hillRealMeanZeroInclusion (hillRealSpatialTranslation t q)) E=
    hillHminusDiscriminant (hillRealMeanZeroInclusion q) E
  rw [hillRealSpatialTranslation_inclusion,hillHminusDiscriminant_spatialTranslation]

/-- Every actual open-coordinate quotient is constant along the entire
physical spatial orbit, by preconnectedness of the time parameter. -/
theorem hillRealSpatialCoordinateRatio_spatialTranslation (n : ℕ+) (q : HillRealMeanZeroSource)
    (s t : ℝ) (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) :
    hillRealSpatialCoordinateRatio n s (hillRealSpatialTranslation t q)=
      hillRealSpatialCoordinateRatio n s q := by
  have hc : Continuous (fun t : ℝ => hillRealSpatialTranslation t q) :=
    continuous_hillRealSpatialTranslation_orbit q
  have h := action_invariant_eq_along_isospectral_family q (hillRealSpatialCoordinateRatio n s)
    (continuousOn_hillRealSpatialCoordinateRatio_on_isoset n s q hq)
    (fun j p _ u => originalHill_spatialCoordinateRatio_actionFlow_invariant j p s u (n:ℤ))
    (fun t : ℝ => hillRealSpatialTranslation t q) hc
    (hillRealDiscriminantData_spatialTranslation q) t 0
  simpa only [hillRealSpatialTranslation_zero] using h

/-- The actual spatial character is continuous in the physical displacement. -/
theorem continuous_hillRealSpatialCoordinateRatio (n : ℕ+) (q : HillRealMeanZeroSource) :
    Continuous (fun s : ℝ => hillRealSpatialCoordinateRatio n s q) := by
  have hc : Continuous (fun t : ℝ => hillRealSpatialTranslation t q) :=
    continuous_hillRealSpatialTranslation_orbit q
  exact ((continuous_hillRealNativeCoordinate (n:ℤ)).comp hc).div_const _

theorem hillRealSpatialCoordinateRatio_zero (n : ℕ+) (q : HillRealMeanZeroSource)
    (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) :
    hillRealSpatialCoordinateRatio n 0 q=1 := by
  simp only [hillRealSpatialCoordinateRatio,hillRealSpatialTranslation_zero,div_self hq]

/-- Exact character multiplication under addition of physical displacements.
No particular winding number is inferred from the character property. -/
theorem hillRealSpatialCoordinateRatio_add (n : ℕ+) (q : HillRealMeanZeroSource)
    (hq : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) (s t : ℝ) :
    hillRealSpatialCoordinateRatio n (s+t) q=
      hillRealSpatialCoordinateRatio n s q*hillRealSpatialCoordinateRatio n t q := by
  have hB := hillNativeCoordinate_ne_zero_on_isoset n q (hillRealSpatialTranslation t q) hq
    (hillRealDiscriminantData_spatialTranslation q t)
  have hmul := hillRealSpatialCoordinateRatio_spatialTranslation n q s t hq
  unfold hillRealSpatialCoordinateRatio at hmul ⊢
  rw [← hillRealSpatialTranslation_add]
  rw [← hmul]
  field_simp

theorem hillRealSpatialCoordinateRatio_periodic (n : ℕ+) (q : HillRealMeanZeroSource) :
    Function.Periodic (fun s : ℝ => hillRealSpatialCoordinateRatio n s q) 1 := by
  intro s
  change hillRealSpatialCoordinateRatio n (s+1) q=hillRealSpatialCoordinateRatio n s q
  unfold hillRealSpatialCoordinateRatio
  rw [← hillRealSpatialTranslation_add,hillRealSpatialTranslation_one]

end NLS.Articles.KdVPseudomeasures
