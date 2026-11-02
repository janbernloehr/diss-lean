import NLS.MKdV.MiuraZeroActionRigidity

/-! # The physical mass trace and the zero-action fiber

These are global dependencies of the article's remaining independent
mKdV action-coordinate geometry. They use the native mass Hamiltonian,
the original signed mean and independently defined physical Hill actions.
They do not assert a global inverse Birkhoff chart or forward factorization.
-/
noncomputable section
open Set NLS.MKdV NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Exact physical K₁ trace on every original real H¹ source. -/
theorem physical_mass_action_trace (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    nativeMiuraMass 1 (miuraH1SobolevEquiv a) = (1/2 : ℂ)*(a.val 0)^2+
      ∑' n : ℕ, (2*(Real.pi : ℂ)*(n+1))*miuraMKdVAction a ha (n+1) := by
  rw [← miuraH1Mass_eq_nativeMiuraMass a]
  have h := (hasSum_miuraMKdVActions_mass a ha).tsum_eq
  linear_combination -h

/-- The same actual actions and signed mean determine the original scalar L² norm. -/
theorem physical_actions_mean_determine_L2_norm (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ‖scalarInclusion a‖^2 = (a.val 0).re^2+
      2*(∑' n : ℕ, (2*(Real.pi : ℂ)*(n+1))*miuraMKdVAction a ha (n+1)).re := by
  rw [(hasSum_miuraH1ActionMoment_physical a ha).tsum_eq]
  exact miuraL2_norm_sq_eq_actions_mean a ha

/-- The positive physical Gardner fields recover translation, with original period-one constants. -/
theorem physical_action_field_trace (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1)) •
      l2GardnerDirection (miuraL2Action (n+1)) (scalarInclusion a)) (periodOneDerivative a) :=
  hasSum_miuraGardnerDirections_spatialDerivative a ha

/-- There is exactly one physical zero-action profile on each original fixed-mean H¹ leaf. -/
theorem physical_zero_action_fiber_unique (a b : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (hb : ∀ j, b.val j = conj (b.val (-j)))
    (hJa : ∀ n : ℕ, 1 ≤ n → miuraMKdVAction a ha n = 0)
    (hJb : ∀ n : ℕ, 1 ≤ n → miuraMKdVAction b hb n = 0)
    (hmean : a.val 0 = b.val 0) : a = b := by
  rw [eq_scalarMode_mean_of_miuraActions_zero a ha hJa,
    eq_scalarMode_mean_of_miuraActions_zero b hb hJb,hmean]

end NLS.Articles.MKdVNLSHierarchies
