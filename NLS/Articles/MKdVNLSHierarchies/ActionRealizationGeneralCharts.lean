import NLS.MKdV.MiuraSobolevActionRealization
import NLS.MKdV.MiuraGeneralNLSActionsCartesianStationarity
import NLS.SequenceSpaces.LocalTailActionFactorAt

/-! # Arbitrary native physical action data and general analytic action charts

Action realization is global on the original native Sobolev domains.
The full NLS action sequence has a holomorphic, rotation-stationary
Cartesian representation near every physical original H1 profile.
Descent to a global forward analytic action-space factor is still separate.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem physical_mKdV_native_action_data_realization (s : ℕ) (hs : 1 ≤ s)
    (J : WeightedCoeff (miuraSpectralActionWeight s) 1)
    (hJ : ∀ n, (J.val n).im = 0 ∧ 0 ≤ (J.val n).re)
    (hzero : ∀ n : ℤ, ¬0 < n → J.val n = 0) (c : ℝ) :
    ∃ a : MiuraRealSobolevSource s, miuraSobolevActionSequence s a.val = J ∧ a.val.val 0 = (c : ℂ) :=
  exists_miuraSobolev_profile_of_nonnegative_actions s hs J hJ hzero c

/-- Arbitrary nonnegative weight-three action data and signed mean are
realized by an original real H1 profile with the independent Hill actions. -/
theorem physical_H1_Hill_action_data_realization
    (J : WeightedCoeff (miuraSpectralActionWeight 1) 1)
    (hJ : ∀ n, (J.val n).im = 0 ∧ 0 ≤ (J.val n).re)
    (hzero : ∀ n : ℤ, ¬0 < n → J.val n = 0) (c : ℝ) :
    ∃ a : ScalarDomain 2, ∃ ha : ∀ j, a.val j = conj (a.val (-j)),
      a.val 0 = (c : ℂ) ∧ ∀ n : ℕ, 1 ≤ n → miuraMKdVAction a ha n = J.val (n : ℤ) := by
  obtain ⟨a,hact,hmean⟩ := exists_miuraSobolev_profile_of_nonnegative_actions 1 le_rfl J hJ hzero c
  let b := miuraH1SobolevEquiv.symm a.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,miuraH1SobolevEquiv_symm_apply] using a.property j
  refine ⟨b,hb,?_,?_⟩
  · simpa only [b,miuraH1SobolevEquiv_symm_apply] using hmean
  · intro n hn
    rw [← miuraSobolevActionSequence_one_eq_physical b hb n hn]
    have he : miuraH1SobolevEquiv b = a.val := miuraH1SobolevEquiv.apply_symm_apply a.val
    rw [he,hact]

/-- The whole original signed NLS action sequence is holomorphic and
stationary under every selected Cartesian rotation in one common complex
L2/half-order inverse chart at each original real H1 profile. -/
theorem physical_NLS_actions_general_H1_Cartesian_chart (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ C : MiuraGeneralCartesianNLSActionChart (miuraPhysicalH1L2Point a ha),
      AnalyticOnNhd ℂ C.observables (Metric.ball (miuraPositiveCartesianMap (scalarInclusion a)) C.radius) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (miuraPositiveCartesianMap (scalarInclusion a)) C.radius,
        fderiv ℂ C.observables z (miuraCartesianActionVector n z) = 0 := by
  obtain ⟨C⟩ := nonempty_miuraGeneralCartesianNLSActionChart a ha
  exact ⟨C,C.observables_analytic,C.observables_rotation_stationary⟩

end NLS.Articles.MKdVNLSHierarchies
