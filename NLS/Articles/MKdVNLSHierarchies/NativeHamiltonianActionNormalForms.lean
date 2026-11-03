import NLS.MKdV.MiuraNativeHamiltonianFrequencies

/-! # Independent native action normal forms toward Theorem 3

The physical Hill K_m has a global holomorphic action normal form on
its exact H^(m-1) domain, including m=1. Positive action derivatives
are intrinsic even at closed actions for m>=2, and the mass derivative
is explicitly 2πn. The comparison with restricted NLS frequencies and
the independent-angle/final angle-sum clause remain separate obligations.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- One common open complex weight-(2m-1) summable action/mean domain
and one holomorphic normal form recover the independent physical K_m
on EVERY real H^(m-1) profile. The domain and factor precede the profile.
Closed actions, arbitrary infinite support, and signed zero mean are included. -/
theorem physical_native_Hill_global_action_normal_form (m : ℕ) (_hm : 1 ≤ m) :
    ∃ V : Set (MiuraNativeActionMeanTarget (m-1)), ∃ F : MiuraNativeActionMeanTarget (m-1) → ℂ,
      IsOpen V ∧ (∀ a : MiuraRealSobolevSource (m-1), miuraNativeActionMeanMap (m-1) a.val ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧ ∀ a : MiuraRealSobolevSource (m-1),
          F (miuraNativeActionMeanMap (m-1) a.val) = miuraSpectralHillHamiltonian (m-1) a.val := by
  obtain ⟨V,F,hV,hall,hF,hrec⟩ := exists_global_native_miuraHamiltonian_action_factor_allOrders (m-1)
  exact ⟨V,F,hV,hall,hF,fun b hb => (hF b hb).restrictScalars (𝕜 := ℝ),hrec⟩

/-- The positive physical action derivatives of K_m are independent of
the normal form chosen, on the full original native real domain, including
a collapsed selected action. This identifies the independent mKdV-side
frequency; equality with the original NLS frequency is not asserted here. -/
theorem physical_native_Hill_action_frequency_intrinsic (m : ℕ) (hm : 2 ≤ m)
    (D E : MiuraNativeHamiltonianActionData (m-1)) (a : MiuraRealSobolevSource (m-1))
    (n : ℕ) (hn : 1 ≤ n) :
    D.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) =
      E.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) :=
  D.frequency_unique E (by omega) a n (by omega)

theorem physical_native_Hill_action_frequency_analytic (m : ℕ) (_hm : 1 ≤ m)
    (D : MiuraNativeHamiltonianActionData (m-1)) (n : ℕ) (_hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (D.frequency (n : ℤ)) D.domain := D.frequency_analytic n

/-- The mass frequency on the full complex order-one action/mean space
is exactly 2πn at every point, with no nonzero-action premise. -/
theorem physical_Hill_mass_action_frequency (b : MiuraActionMeanTarget) (n : ℕ) (_hn : 1 ≤ n) :
    fderiv ℂ miuraMassActionFactor b (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) =
      2*(Real.pi : ℂ)*n := by
  simpa only [Int.cast_natCast] using fderiv_miuraMassActionFactor_single b (n : ℤ)

end NLS.Articles.MKdVNLSHierarchies
