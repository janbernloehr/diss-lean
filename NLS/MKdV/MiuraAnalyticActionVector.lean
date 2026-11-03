import NLS.MKdV.MiuraCartesianJacobianCoordinates
import NLS.MKdV.MiuraActionIndependence

/-! # An analytic L2 extension of each physical Gardner action field -/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraAnalyticActionVector (n : ℕ) (a : Coeff 2) : Coeff 2 :=
  (sourceActionDifferenceVector n (-(n : ℤ)) (scalarL2Diagonal a)).fst

theorem analyticAt_miuraAnalyticActionVector (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) :
    AnalyticAt ℂ (miuraAnalyticActionVector n) a := by
  let φ : realTypeSourceSubmodule 2 := ⟨scalarL2Diagonal a,(scalarL2Diagonal_realDiagonal a ha).1⟩
  have hf : AnalyticAt ℂ (sourceActionDifferenceVector n (-(n : ℤ))) (scalarL2Diagonal a) :=
    analyticAt_sourceActionDifferenceVector n (-(n : ℤ)) φ
  let P : CoeffPair 2 →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).comp (CoeffPair.toMax 2).toContinuousLinearMap
  exact (P.analyticAt _).comp (hf.comp (scalarL2Diagonal.analyticAt a))

theorem miuraAnalyticActionVector_eq_Gardner (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraAnalyticActionVector n (scalarInclusion a) =
      l2GardnerDirection (miuraL2Action n) (scalarInclusion a) := by
  have he := miuraActionDifference_direction a ha n hn
  unfold miuraAnalyticActionVector sourceActionDifferenceVector sourceHamiltonianVector
  rw [scalarL2Diagonal_scalarInclusion,← map_sub,he,scalarL2Diagonal_fst]

theorem miuraCartesian_analytic_action_covariance (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
        (miuraAnalyticActionVector n (scalarInclusion a)) =
      miuraCartesianActionVector n (miuraPositiveCartesianMap (scalarInclusion a)) := by
  rw [miuraAnalyticActionVector_eq_Gardner a ha n hn]
  exact miuraCartesianJacobian_Gardner_action a ha n hn

theorem miuraAnalyticActionVector_eq_zero_of_action_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) : miuraAnalyticActionVector n (scalarInclusion a) = 0 := by
  rw [miuraAnalyticActionVector_eq_Gardner a ha n hn]
  exact miuraGardnerDirection_eq_zero_of_action_zero a ha n hn hzero

end NLS.MKdV
