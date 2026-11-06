import NLS.MKdV.MiuraNativeSpatialTranslation
import NLS.MKdV.QuasiHillPeriodicBasepoint
import NLS.MKdV.MiuraHillDirichletComparison
import NLS.Fourier.SpatialTranslation

/-! # Literal physical profiles of native Miura spatial translations

The positive Fourier phase is exactly translation of the original
continuous period-one H¹ representative. The independently constructed
translated quasi-Hill characteristic is thus the actual native Hill
Dirichlet characteristic, at every complex energy.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

def miuraNativePeriodicProfile (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) : C(ℝ,ℂ) :=
  ⟨fun x => periodOneSobolevSynthesis (hierarchySobolevToScalarDomain s hs a.val)
      (x : AddCircle (2:ℝ)),
    continuous_periodOneSobolevSynthesis (hierarchySobolevToScalarDomain s hs a.val)⟩

theorem miuraNativePeriodicProfile_periodic (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    Function.Periodic (miuraNativePeriodicProfile s hs a) 1 :=
  periodOneSobolevSynthesis_periodic (hierarchySobolevToScalarDomain s hs a.val)

theorem miuraNativePeriodicProfile_unit (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    periodicScalarProfileUnitCurve (miuraNativePeriodicProfile s hs a) =
      periodOneMiuraCurve (hierarchySobolevToScalarDomain s hs a.val) := by
  ext t
  exact (periodOneMiuraCurve_apply _ t).symm

theorem miuraNativePeriodicProfile_spatialTranslation
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (τ : ℝ) :
    miuraNativePeriodicProfile s hs (miuraNativeSpatialTranslation s τ a) =
      periodicScalarProfileTranslate (miuraNativePeriodicProfile s hs a) τ := by
  have hc : WeightedCoeff.sobolevToL1CLM 2 (by simp)
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val) =
      Coeff.spatialTranslation (2*Real.pi) τ
        (WeightedCoeff.sobolevToL1CLM 2 (by simp) (hierarchySobolevToScalarDomain s hs a.val)) := by
    ext k
    simp only [WeightedCoeff.sobolevToL1CLM_apply,hierarchySobolevToScalarDomain_apply,
      Coeff.spatialTranslation_apply,miuraNativeSpatialTranslation,WeightedCoeff.spatialTranslation_apply]
  ext x
  change periodOneSobolevSynthesis _ (x : AddCircle (2:ℝ)) =
    periodOneSobolevSynthesis _ ((x+τ : ℝ) : AddCircle (2:ℝ))
  rw [periodOneSobolevSynthesis_apply,periodOneSobolevSynthesis_apply,hc,
    periodOneSynthesis_spatialTranslation]

theorem miuraNativeHillDirichletCharacteristic_spatialTranslation
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (τ : ℝ) (E : ℂ) :
    hillL2DirichletCharacteristic (sobolevMiuraHillPotential
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val)) E =
      quasiHillDirichletCharacteristic (periodicScalarProfileUnitCurve
        (periodicScalarProfileTranslate (miuraNativePeriodicProfile s hs a) τ)) E := by
  rw [hillL2DirichletCharacteristic_miura,← miuraNativePeriodicProfile_unit,
    miuraNativePeriodicProfile_spatialTranslation]

end NLS.MKdV
