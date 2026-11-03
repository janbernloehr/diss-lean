import NLS.MKdV.MiuraCartesianGardnerAction
import NLS.MKdV.MiuraSobolevCartesianActionFlow

/-! # Exact Cartesian action rotations and mixed Gardner brackets

The complete native Cartesian pair has the literal unit-speed rotation
law along each actual Gardner action orbit. Its signed mean and full
native action sequence are fixed. The mixed Cartesian-action brackets
hold on original real H¹ without any open-action assumption. General
Cartesian-Cartesian brackets, global inverse geometry, independent angle
construction and the remaining factorization/frequency claims stay open.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem native_cartesian_complete_action_rotation (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (∀ m : ℕ, 1 ≤ m →
      miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s (miuraActionFlow s a ha n t)) =
        if m = n then cartesianPlaneRotation t (miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s a))
        else miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s a)) ∧
      (miuraSobolevPositiveCartesianMap s (miuraActionFlow s a ha n t)).2 =
        (miuraSobolevPositiveCartesianMap s a).2 ∧
      miuraSobolevActionSequence s (miuraActionFlow s a ha n t) = miuraSobolevActionSequence s a :=
  ⟨fun m hm => miuraSobolevPositiveCartesianMap_actionFlow_eval s a ha m n hm hn t,
    miuraSobolevPositiveCartesianMap_actionFlow_mean s a ha n t,
    miuraSobolevActionSequence_miuraActionFlow s a ha n t⟩

theorem cartesian_action_Gardner_brackets_original_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (l2GardnerBracket (fun b => (miuraL2CartesianCoordinates m b).1) (miuraL2Action n) (scalarInclusion a),
     l2GardnerBracket (fun b => (miuraL2CartesianCoordinates m b).2) (miuraL2Action n) (scalarInclusion a)) =
      if m = n then ((miuraL2CartesianCoordinates m (scalarInclusion a)).2,
        -(miuraL2CartesianCoordinates m (scalarInclusion a)).1) else 0 :=
  miuraCartesianActionGardner_brackets a ha m n hm hn

theorem original_L2_zero_energy_trace (a : Coeff 2) :
    canonicalDiscriminant (by simp) (periodOnePotential (scalarL2Diagonal a)) 0 = 2*cosh (a 0) :=
  canonicalDiscriminant_scalarL2_zero a

theorem native_original_NLS_actions_constant_on_Gardner_orbits (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) (k : ℤ) :
    sourceComplexAction (by simp) (by norm_num) k
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) (miuraActionFlow s a ha n t))) =
    sourceComplexAction (by simp) (by norm_num) k
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)) :=
  miuraNLSAction_allSobolev_miuraActionFlow s a ha n t k

end NLS.Articles.MKdVNLSHierarchies
