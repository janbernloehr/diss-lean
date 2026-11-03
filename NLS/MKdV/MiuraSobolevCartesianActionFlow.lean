import NLS.MKdV.MiuraRealSobolevCartesianMap
import NLS.MKdV.MiuraL2ZeroEnergyFlowMean

/-! # Full native Cartesian covariance and conserved action sequences

Every positive coefficient has the exact physical rotation law, the
signed mean is fixed, and the entire native weighted action sequence is
invariant. All original signed NLS actions are invariant on these same
complete physical orbits. No open-action hypothesis is imposed.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevPositiveCartesianMap_positive (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s a) =
      miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) := by
  change ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a).1).val.val m,
    (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a).2).val.val m) = _
  rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,
    if_pos (by omega : (0 : ℤ) < m),if_pos (by omega : (0 : ℤ) < m)]
  exact miuraSobolevCartesianSequence_positive s a ha m hm

theorem miuraSobolevPositiveCartesianMap_actionFlow_eval (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s (miuraActionFlow s a ha n t)) =
      if m = n then cartesianPlaneRotation t (miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s a))
      else miuraSobolevPositiveEval s m (miuraSobolevPositiveCartesianMap s a) := by
  rw [miuraSobolevPositiveCartesianMap_positive s _ (miuraActionFlow_real s a ha n t) m hm,
    miuraSobolevPositiveCartesianMap_positive s a ha m hm]
  exact miuraL2CartesianCoordinates_miuraActionFlow s a ha m n hm hn t

theorem miuraSobolevPositiveCartesianMap_actionFlow_mean (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    (miuraSobolevPositiveCartesianMap s (miuraActionFlow s a ha n t)).2 =
      (miuraSobolevPositiveCartesianMap s a).2 :=
  miuraActionFlow_mean_allSobolev s a ha n t

/-- Conservation holds as equality in the entire actual native weighted
summable action space, including every collapsed selected action. -/
theorem miuraSobolevActionSequence_miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraSobolevActionSequence s (miuraActionFlow s a ha n t) = miuraSobolevActionSequence s a := by
  let b := miuraActionFlow s a ha n t
  have hb := miuraActionFlow_real s a ha n t
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraSobolevActionSequence_domain s
  apply Subtype.ext
  funext k
  by_cases hk : 0 < k
  · rw [hcoord b (hreal hb) k hk,hcoord a (hreal ha) k hk,
      miuraSobolevActionSource_eq_L2_diagonal,miuraSobolevActionSource_eq_L2_diagonal,
      ← miuraActionInitialSource_L2_diagonal s b hb,← miuraActionInitialSource_L2_diagonal s a ha]
    exact congrArg (fun z : ℂ => (1/2 : ℂ)*z)
      (sourceDiagonalLaurentAction_eq_of_isospectral (by simp) (by norm_num)
        (miuraActionInitialDiagonalSource s a ha) (miuraActionInitialDiagonalSource s b hb)
        (miuraActionFlow_isospectral s a ha n t) k 0 (ne_of_gt hk))
  · rw [miuraSobolevActionSequence_nonpositive s b k hk,miuraSobolevActionSequence_nonpositive s a k hk]

/-- Every original signed NLS action is fixed along each complete scalar
action orbit, for every integer Sobolev order, including original L². -/
theorem miuraNLSAction_allSobolev_miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) (k : ℤ) :
    sourceComplexAction (by simp) (by norm_num) k
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) (miuraActionFlow s a ha n t))) =
    sourceComplexAction (by simp) (by norm_num) k
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)) := by
  let b := miuraActionFlow s a ha n t
  have hb := miuraActionFlow_real s a ha n t
  rw [← miuraActionInitialSource_L2_diagonal s b hb,← miuraActionInitialSource_L2_diagonal s a ha,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) k _ (miuraActionInitialSource s b hb).property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) k _ (miuraActionInitialSource s a ha).property]
  exact sourceRealAction_eq_of_isospectral (by simp) (by norm_num) _ _ (miuraActionFlow_isospectral s a ha n t) k

end NLS.MKdV
