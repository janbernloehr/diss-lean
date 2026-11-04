import NLS.MKdV.MiuraFiniteGapFullPhaseLieContinuity
import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.SequenceSpaces.WeightedSpatialTranslationContinuity

/-! # Actual spatial translation in the native real Miura spaces

The norm-continuous period-one Fourier translation preserves the actual
indexed Hill spectrum and each fixed closed-gap complement. It therefore
stays inside the finite-gap strata used by full-phase Lie continuity.
-/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraNativeSpatialTranslation_real (s : ℕ) (t : ℝ) (a : MiuraRealSobolevSource s) :
    ∀ k,(WeightedCoeff.spatialTranslation (Weight.sobolev (s:ℝ)) (2*Real.pi) t a.val).val k =
      conj ((WeightedCoeff.spatialTranslation (Weight.sobolev (s:ℝ)) (2*Real.pi) t a.val).val (-k)) := by
  intro k
  simp only [WeightedCoeff.spatialTranslation_apply,map_mul]
  rw [a.property k,← Complex.exp_conj]
  congr 1
  simp [map_ofNat]

def miuraNativeSpatialTranslation (s : ℕ) (t : ℝ) (a : MiuraRealSobolevSource s) : MiuraRealSobolevSource s :=
  ⟨WeightedCoeff.spatialTranslation (Weight.sobolev (s:ℝ)) (2*Real.pi) t a.val,
    miuraNativeSpatialTranslation_real s t a⟩

@[simp] theorem miuraNativeSpatialTranslation_zero (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraNativeSpatialTranslation s 0 a = a := by
  apply Subtype.ext
  exact WeightedCoeff.phaseFlow_zero _ _ _

theorem continuous_miuraNativeSpatialTranslation (s : ℕ) (a : MiuraRealSobolevSource s) :
    Continuous (fun t => miuraNativeSpatialTranslation s t a) := by
  have hp : Continuous (fun t : ℝ => (t,a.val)) := continuous_id.prodMk continuous_const
  have hc := (WeightedCoeff.continuous_spatialTranslation (Weight.sobolev (s:ℝ))
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (2*Real.pi)).comp hp
  exact hc.subtype_mk (fun t => miuraNativeSpatialTranslation_real s t a)

theorem miuraNativeSpatialTranslation_original_source (s : ℕ) (t : ℝ) (a : MiuraRealSobolevSource s) :
    (miuraActionInitialSource s (miuraNativeSpatialTranslation s t a).val
      (fun k => (miuraNativeSpatialTranslation s t a).property k)).val =
    sourceSpatialTranslation t (miuraActionInitialSource s a.val (fun k => a.property k)).val := by
  rw [miuraActionInitialSource_L2_diagonal,miuraActionInitialSource_L2_diagonal]
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · change (scalarL2Diagonal _).fst = (sourceSpatialTranslation t (scalarL2Diagonal _)).fst
    rw [sourceSpatialTranslation_fst,scalarL2Diagonal_fst,scalarL2Diagonal_fst]
    ext k
    rw [hierarchySobolevJetL2_apply,Coeff.spatialTranslation_apply,hierarchySobolevJetL2_apply]
    simp only [pow_zero,one_mul]
    exact WeightedCoeff.spatialTranslation_apply _ _ _ _ k
  · change (scalarL2Diagonal _).snd = (sourceSpatialTranslation t (scalarL2Diagonal _)).snd
    rw [sourceSpatialTranslation_snd,scalarL2Diagonal_snd,scalarL2Diagonal_snd]
    ext k
    rw [hierarchySobolevJetL2_apply,Coeff.spatialTranslation_apply,hierarchySobolevJetL2_apply]
    simp only [pow_zero,one_mul]
    exact WeightedCoeff.spatialTranslation_apply _ _ _ _ k

theorem miuraNativeSpatialTranslation_H1Source_isospectral (s : ℕ) (hs : 1 ≤ s)
    (t : ℝ) (a : MiuraRealSobolevSource s) :
    realDiagonalH1Source
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s t a).val)
      (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s t a)) ∈
      sourceIsospectralSet (by simp)
        (realDiagonalH1Source (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)) := by
  rw [miuraNativeH1Source_eq_originalSource,miuraNativeH1Source_eq_originalSource]
  constructor
  · rw [miuraNativeSpatialTranslation_original_source]
    exact sourcePeriodicSpectrum_spatialTranslation (by simp) t _
  · intro z
    rw [miuraNativeSpatialTranslation_original_source]
    exact sourcePeriodicAlgebraicMultiplicity_spatialTranslation (by simp) t _ z

theorem miuraNativeHillLabels_spatialTranslation (s : ℕ) (hs : 1 ≤ s)
    (t : ℝ) (a : MiuraRealSobolevSource s) :
    miuraHillLabels (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s t a).val)
      (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s t a)) =
    miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) :=
  miuraHillLabels_eq_of_isospectral _ _ _ _ (miuraNativeSpatialTranslation_H1Source_isospectral s hs t a)

theorem miuraNativeClosedComplement_spatialTranslation (s : ℕ) (hs : 1 ≤ s)
    (F : Finset ℕ) (a : MiuraRealSobolevSource s) (ha : a ∈ miuraNativeClosedComplement s hs F) (t : ℝ) :
    miuraNativeSpatialTranslation s t a ∈ miuraNativeClosedComplement s hs F := by
  intro k hk
  have hl := miuraNativeHillLabels_spatialTranslation s hs t a
  exact (congrFun (hillRealGapHalfLength_eq_of_labels
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s t a).val)
      (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s t a)))
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)) hl) (k+1)).trans (ha k hk)

end NLS.MKdV
