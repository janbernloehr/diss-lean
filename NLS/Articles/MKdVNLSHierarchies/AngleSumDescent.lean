import NLS.MKdV.MiuraOpenGardnerPhaseFactor

/-! # The global descent step in Theorem 4(iii)

This file proves the phase-sum implication for any independently supplied
actual H¹ unit phase with the original negative Gardner generators. The
hypotheses concern its actual differential, not a prescribed value or an
action factor. The selected physical action alone must be open. The
independent original mKdV phase must still be constructed and identified
before this implication completes the article's final clause.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Every continuous invariant of all actual Gardner action flows is a
function of the complete physical action sequence and literal signed mean. -/
theorem physical_complete_action_flow_invariant_factor (s : ℕ) (hs : 1 ≤ s)
    (F : MiuraRealSobolevSource s → ℂ) (hF : Continuous F)
    (hflow : ∀ a n, 1 ≤ n → ∀ t : ℝ, F (miuraNativeRealActionFlow s a n t) = F a) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) = F a :=
  exists_miuraContinuousObservable_action_factor s hs F hF hflow

/-- The full unit-phase form of the final angle-sum implication, on
exactly its physical selected open-action domain and with all other
actions allowed closed. The independent phase's actual Gardner generator
identity is the explicit remaining input, not an assumed factorization. -/
theorem theorem4_iii_phase_sum_descent_of_independent_Gardner_phase
    (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : 1 ≤ m) (F : ScalarDomain 2 → ℂ)
    (P : ∀ a : MiuraRealSobolevSource s,
      miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) ≠ 0 →
      SobolevGardnerGradientAt F (hierarchySobolevToScalarDomain s hs a.val))
    (hunit : ∀ a : MiuraRealSobolevSource s,
      miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) ≠ 0 →
      ‖F (hierarchySobolevToScalarDomain s hs a.val)‖ = 1)
    (hgen : ∀ (a : MiuraRealSobolevSource s)
      (ha : miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) ≠ 0),
      ∀ n : ℕ, 1 ≤ n →
      reflectedHilbertPairing (scalarInclusion (P a ha).gradient)
        (l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)) =
          -(if m = n then I else 0)*F (hierarchySobolevToScalarDomain s hs a.val)) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) ≠ 0 →
      f (miuraNativeActionMeanMap s a.val) =
        miuraNativeNLSUnitPhase s m a*F (hierarchySobolevToScalarDomain s hs a.val) := by
  have ho (a : MiuraRealSobolevSource s) : miuraNativeNLSAngularCoordinate s m a ≠ 0 ↔
      miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) ≠ 0 :=
    not_congr (miuraNativeNLSAngularCoordinate_zero_iff_physical_action_zero s m hm a)
  obtain ⟨f,hf⟩ := exists_independent_open_Gardner_phase_action_factor s hs m hm F
    (fun a ha => P a ((ho a).mp ha)) (fun a ha => hunit a ((ho a).mp ha))
    (fun a ha n hn => hgen a ((ho a).mp ha) n hn)
  exact ⟨f,fun a ha => hf a ((ho a).mpr ha)⟩

end NLS.Articles.MKdVNLSHierarchies
