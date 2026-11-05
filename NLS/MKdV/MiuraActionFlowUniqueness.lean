import NLS.MKdV.MiuraActionFlowInvariants
import NLS.MKdV.MiuraActionReflection

/-! # Intrinsic uniqueness and closed-action stationarity

Every competing real H1 curve solving the actual Gardner action equation
with the same initial value is the constructed complete trajectory.
Closed selected gaps give exactly the stationary trajectory.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraH1ActionFlow_unique (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (g : ℝ → ScalarDomain 2) (hgReal : ∀ t j, (g t).val j = conj ((g t).val (-j)))
    (hzero : g 0 = a)
    (hg : ∀ t, HasDerivAt (fun r => scalarInclusion (g r))
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion (g t))) t) :
    g = miuraH1ActionFlow a ha n := by
  let G : ℝ → CoeffPair 2 := fun r => scalarL2Diagonal (scalarInclusion (g r))
  have hd (r : ℝ) : HasDerivAt G (sourceActionDifferenceVector n (-(n : ℤ)) (G r)) r := by
    have h := (scalarL2Diagonal.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r (hg r)
    change HasDerivAt G (scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion (g r)))) r at h
    have hv : sourceActionDifferenceVector n (-(n : ℤ)) (G r) =
        scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion (g r))) := by
      dsimp only [G]
      rw [scalarL2Diagonal_scalarInclusion]
      unfold sourceActionDifferenceVector sourceHamiltonianVector
      rw [← map_sub]
      exact miuraActionDifference_direction (g r) (hgReal r) n hn
    rw [← hv] at h
    exact h
  have hz : G 0 = (realDiagonalH1Source a ha).val := by
    dsimp only [G]
    rw [hzero,scalarL2Diagonal_scalarInclusion]
    rfl
  have he := miuraActionFlowFamily.data.hilbertPairedActionFlow_unique
    (realDiagonalH1Source a ha) n (-(n : ℤ)) G hz hd
  funext t
  apply realDiagonalH1Source_injective _ _ (hgReal t) (miuraH1ActionFlow_real a ha n t)
  apply Subtype.ext
  rw [miuraH1ActionFlow_source]
  change sobolevSourceInclusion (g t,g t) = _
  simpa only [G,scalarL2Diagonal_scalarInclusion] using congrFun he t

theorem miuraH1ActionFlow_eq_self_of_action_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) (t : ℝ) : miuraH1ActionFlow a ha n t = a := by
  let D := miuraActionFlowFamily.data
  let φ := realDiagonalH1Source a ha
  have hi : miuraNLSAction a n = 0 := (miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.mp hzero
  have hneg : miuraNLSAction a (-(n : ℤ)) = 0 := (miuraNLSAction_reflection a ha n).trans hi
  have hpair (k : ℤ) (hk : miuraNLSAction a k = 0) : RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k = 0 := by
    rw [D.hilbert_pairAction_eq]
    have hreal : sourceRealAction (by simp) (by norm_num) φ.val φ.property k = 0 :=
      (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) k φ.val φ.property).symm.trans hk
    rw [hreal]
    rfl
  have hs : D.hilbertPairedActionFlow φ n (-(n : ℤ)) t = φ := by
    apply D.hilbertRealHomeomorph.injective
    rw [D.hilbertRealHomeomorph_pairedActionFlow,RealCoeff.pairedActionRotation,
      RealCoeff.actionRotation_eq_self_of_action_zero _ _ (hpair n hi) t,
      RealCoeff.actionRotation_eq_self_of_action_zero _ _ (hpair (-(n : ℤ)) hneg) (-t)]
  apply realDiagonalH1Source_injective _ _ (miuraH1ActionFlow_real a ha n t) ha
  rw [miuraH1ActionFlow_source]
  exact hs

end NLS.MKdV
