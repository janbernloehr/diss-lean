import NLS.MKdV.MiuraNativeEndpointRelease
import NLS.KdV.HillDirichletInteriorSheet

/-! # Actual spatial translates with interior open-gap divisors

Every finite set of open contributing gaps has nonzero actual Dirichlet
sheets at all sufficiently small positive spatial translates. The curve
converges in the original native Sobolev norm and retains the full spectrum.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

def miuraNativeHillPotential (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) : RealPeriodOneHillPotential :=
  realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)

theorem miuraNativeDirichletSheetRoot_spatialTranslation_eventually_ne_zero
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 k ≠ 0) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).val)
      (hillDirichletEnergy (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).val
        (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.1
        (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.2 k hk) ≠ 0 := by
  have hends : miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k-1) ≠
      miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k) := by
    intro he
    apply hgap
    change (miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k)-miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k-1))/2 = 0
    rw [he,sub_self,zero_div]
  have hleft := miuraNativeDirichletCharacteristic_open_endpoint_eventually_ne_zero s hs a k hk hends _ (Or.inl rfl)
  have hright := miuraNativeDirichletCharacteristic_open_endpoint_eventually_ne_zero s hs a k hk hends _ (Or.inr rfl)
  filter_upwards [hleft,hright] with τ hl hr
  apply hillDirichletSheetRoot_ne_zero_of_endpoint_characteristics _ k hk
  · change hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff
        (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val) (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s τ a))).val) _ ≠ 0
    rw [realSobolevMiuraHillPotential_toCoeff]
    change hillL2DirichletCharacteristic _ (miuraHillLabels (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val) (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s τ a)) (2*k-1)) ≠ 0
    rw [congrFun (miuraNativeHillLabels_spatialTranslation s hs τ a) (2*k-1)]
    exact hl
  · change hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff
        (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val) (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s τ a))).val) _ ≠ 0
    rw [realSobolevMiuraHillPotential_toCoeff]
    change hillL2DirichletCharacteristic _ (miuraHillLabels (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val) (miuraNativeH1Profile_real s hs (miuraNativeSpatialTranslation s τ a)) (2*k)) ≠ 0
    rw [congrFun (miuraNativeHillLabels_spatialTranslation s hs τ a) (2*k)]
    exact hr

theorem miuraNativeFiniteDirichletSheets_spatialTranslation_eventually_ne_zero
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (F : Finset ℕ)
    (hgap : ∀ k ∈ F,hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 (k+1) ≠ 0) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),∀ k ∈ F,hillDirichletSheetRoot
      (SpectralWeight.one.toCoeff (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).val)
      (hillDirichletEnergy (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).val
        (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.1
        (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.2 (k+1) (by omega)) ≠ 0 := by
  exact (Finset.eventually_all F).mpr (fun k hk =>
    miuraNativeDirichletSheetRoot_spatialTranslation_eventually_ne_zero s hs a (k+1) (by omega) (hgap k hk))

end NLS.MKdV
