import NLS.MKdV.MiuraNativePeriodicProfile
import NLS.MKdV.MiuraOpenEndpointMonodromy
import NLS.MKdV.QuasiHillTerminalTranslation

/-! # Actual native translations remove every open-gap endpoint terminal

At each of the two fixed endpoints of an actual open gap, the translated
original Hill Dirichlet characteristic is nonzero for every sufficiently
small positive translation. No parabolic or genericity hypothesis is added.
-/
noncomputable section
open Set Complex Matrix Filter Topology NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.MKdV

theorem miuraHillLabels_pos (a : ScalarDomain 2) (ha : ∀ m,a.val m = conj (a.val (-m)))
    (j : ℕ) (hj : 1 ≤ j) : 0 < miuraHillLabels a ha j := by
  let q := realSobolevMiuraHillPotential a ha
  have h01 := hillRealLabels_band_strict q.val q.property.1 q.property.2 0
  have h0 := miuraHillLabels_nonnegative a ha 0
  have h1j := monotone_miuraHillLabels a ha hj
  change miuraHillLabels a ha 0 < miuraHillLabels a ha 1 at h01
  exact lt_of_lt_of_le (lt_of_le_of_lt h0 h01) h1j

theorem continuous_miuraNativeDirichletCharacteristic_spatialTranslation
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (E : ℂ) :
    Continuous (fun τ => hillL2DirichletCharacteristic (sobolevMiuraHillPotential
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val)) E) := by
  have hU : Continuous (fun τ => periodOneMiuraCurve
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val)) :=
    (periodOneMiuraCurveCLM.continuous.congr (fun b => periodOneMiuraCurveCLM_apply b)).comp
      ((hierarchySobolevToScalarDomain s hs).continuous.comp
        (continuous_subtype_val.comp (continuous_miuraNativeSpatialTranslation s a)))
  have hc := analyticOnNhd_quasiHillDirichletCharacteristic_joint.continuous.comp
    ((show Continuous (fun _ : ℝ => E) from continuous_const).prodMk hU)
  apply hc.congr
  intro τ
  exact (hillL2DirichletCharacteristic_miura _ E).symm

theorem miuraNativeDirichletCharacteristic_open_endpoint_eventually_ne_zero
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (k : ℕ) (hk : 1 ≤ k)
    (hgap : miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k-1) ≠
      miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k))
    (E : ℂ) (hE : E = (miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val)
        (miuraNativeH1Profile_real s hs a) (2*k-1) : ℂ) ∨
      E = (miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) (2*k) : ℂ)) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),hillL2DirichletCharacteristic (sobolevMiuraHillPotential
      (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s τ a).val)) E ≠ 0 := by
  let b := hierarchySobolevToScalarDomain s hs a.val
  have hb := miuraNativeH1Profile_real s hs a
  by_cases hD : hillL2DirichletCharacteristic (sobolevMiuraHillPotential b) E = 0
  · obtain ⟨c,hc,hM⟩ := miuraQuasiHillMonodromy_open_Dirichlet_endpoint b hb k hk hgap E hE hD
    have hE0 : E ≠ 0 := by
      rcases hE with rfl | rfl
      · exact ofReal_ne_zero.mpr (miuraHillLabels_pos b hb (2*k-1) (by omega)).ne'
      · exact ofReal_ne_zero.mpr (miuraHillLabels_pos b hb (2*k) (by omega)).ne'
    have hz : Complex.sqrt E ≠ 0 := by
      intro hz
      have he := complex_sqrt_sq E
      rw [hz,zero_pow (by norm_num)] at he
      exact hE0 he.symm
    have hpar : quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve (miuraNativePeriodicProfile s hs a))
        ((Complex.sqrt E)^2) 1 = !![(-1:ℂ)^k,0;c,(-1:ℂ)^k] := by
      rw [miuraNativePeriodicProfile_unit,complex_sqrt_sq]
      exact hM
    have hr := quasiHillDirichletCharacteristic_translate_parabolic_eventually_ne_zero
      (miuraNativePeriodicProfile s hs a) (miuraNativePeriodicProfile_periodic s hs a)
      (Complex.sqrt E) hz ((-1)^k) c hc hpar
    rw [complex_sqrt_sq] at hr
    filter_upwards [hr] with τ hτ
    rw [miuraNativeHillDirichletCharacteristic_spatialTranslation]
    exact hτ
  · have h0 : hillL2DirichletCharacteristic (sobolevMiuraHillPotential
        (hierarchySobolevToScalarDomain s hs (miuraNativeSpatialTranslation s 0 a).val)) E ≠ 0 := by
      rw [miuraNativeSpatialTranslation_zero]
      exact hD
    exact ((continuous_miuraNativeDirichletCharacteristic_spatialTranslation s hs a E).continuousAt.eventually_ne h0).filter_mono nhdsWithin_le_nhds

end NLS.MKdV
