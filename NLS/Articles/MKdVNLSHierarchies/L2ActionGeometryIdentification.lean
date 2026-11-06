import NLS.MKdV.MiuraL2ActionProperness

/-! # Original L² endpoint action geometry

The actual Laurent action extensions have their full native norm and
retain the physical Hill coordinates on original real H¹ inputs. The
native K₁ trace holds on every real L² input. The entire action and signed
mean map is proper in L², hence has compact fibers. This is global action
geometry without asserting a global inverse mKdV Birkhoff chart.
-/
noncomputable section
open Set NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Native K₁ is the convergent first spectral action moment plus the literal mean square. -/
theorem native_L2_mass_action_trace (u : ScalarSobolev 0)
    (hu : ∀ j, u.val j = conj (u.val (-j))) :
    nativeMiuraHillHamiltonian 0 u = (1/2 : ℂ)*(u.val 0)^2+
      ∑' n : ℕ, (2*(Real.pi : ℂ)*(n+1))*
        miuraL2Action (n+1) (hierarchySobolevJetL2 0 0 le_rfl u) := by
  let a := hierarchySobolevJetL2 0 0 le_rfl u
  have ha : ∀ j, a j = conj (a (-j)) := by
    intro j
    simpa only [a,hierarchySobolevJetL2_apply,pow_zero,one_mul] using hu j
  rw [nativeMiuraHillHamiltonian_zero_eq_L2Mass,miuraL2Mass_eq_mean_sq_add_actionMoment _ ha,
    ← (hasSum_miuraL2ActionMoment a ha).tsum_eq]
  simp only [a,hierarchySobolevJetL2_apply,pow_zero,one_mul]

/-- The complete original real L² action and signed-mean map is proper in its native target norm. -/
theorem native_L2_action_mean_map_proper : IsProperMap miuraRealL2ActionMeanMap :=
  isProperMap_miuraRealL2ActionMeanMap

/-- Complete action and mean fibers are compact in the original scalar L² topology. -/
theorem native_L2_action_mean_fiber_compact (z : WeightedCoeff (Weight.sobolev 1) 1 × ℂ) :
    IsCompact {a : MiuraRealL2 | miuraRealL2ActionMeanMap a = z} :=
  isCompact_miuraRealL2ActionMeanFiber z

/-- The endpoint action map agrees with the independent physical Hill contour at every original H¹ input. -/
theorem native_L2_action_sequence_physical_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraL2ActionSequence (scalarInclusion a)).val (n : ℤ) = miuraMKdVAction a ha n := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  rw [hcoord _ (hreal (by intro j; simpa only [scalarInclusion_apply] using ha j)) n hn,
    miuraL2Action_eq_physical a ha n hn]

end NLS.Articles.MKdVNLSHierarchies
