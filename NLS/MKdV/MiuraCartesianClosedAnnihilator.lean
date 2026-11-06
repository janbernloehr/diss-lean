import NLS.MKdV.MiuraAnalyticActionVector
import NLS.ComplexAnalysis.ClosedEquivarianceAnnihilator
import NLS.SequenceSpaces.PositiveCartesianCotangentModes

/-! # Closed-mode constraints on an annihilator of the full Jacobian -/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesian_closed_annihilator_rotation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    (L.comp (miuraCartesianActionVector n)).comp
      (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0 := by
  let V := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2
  have hw : ∀ k : ℤ, Weight.sobolev 1 (-k) = Weight.sobolev 1 k := by intro k; simp
  have hspan (h : ScalarDomain 2) : ∃ x y : V, h = x.val+I • y.val :=
    ⟨WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw h,
      WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw ((-I) • h),
        WeightedCoeff.physicalRealPart_complex_decomp _ hw h⟩
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have h := NLS.ComplexAnalysis.annihilator_rotation_of_stationary_equivariance V hspan
    scalarInclusion (miuraCartesianActionVector n) miuraPositiveCartesianMap (miuraAnalyticActionVector n)
    ⟨a,ha⟩ (analyticAt_miuraPositiveCartesianMap _ har)
    (analyticAt_miuraAnalyticActionVector _ har n).differentiableAt
    (fun b => miuraCartesian_analytic_action_covariance b.val b.property n hn)
    (miuraAnalyticActionVector_eq_zero_of_action_zero a ha n hn hzero) L hL
  let Q := (L.comp (miuraCartesianActionVector n)).comp
    (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a))
  change Q.comp scalarInclusion = 0 at h
  change Q = 0
  apply ContinuousLinearMap.ext
  apply congrFun
  apply (scalarInclusion_denseRange (p := 2) (by simp)).equalizer Q.continuous continuous_const
  funext u
  exact congrArg (fun T : ScalarDomain 2 →L[ℂ] ℂ => T u) h

theorem miuraCartesianJacobian_own_Gardner_pairs (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraPositiveCartesianEval n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianX n) (scalarInclusion a))) = (0,-1) ∧
    miuraPositiveCartesianEval n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraCartesianY n) (scalarInclusion a))) = (1,0) := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hf := (analyticAt_miuraL2CartesianCoordinates _ har n hn).differentiableAt
  have hXX : l2GardnerBracket (miuraCartesianX n) (miuraCartesianX n) (scalarInclusion a) = 0 :=
    miuraCartesianGardnerBracket_self a ha n hn (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hYY : l2GardnerBracket (miuraCartesianY n) (miuraCartesianY n) (scalarInclusion a) = 0 :=
    miuraCartesianGardnerBracket_self a ha n hn (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hXY := miuraCartesianPlane_Gardner_canonical a ha n hn
  have hYX : l2GardnerBracket (miuraCartesianY n) (miuraCartesianX n) (scalarInclusion a) = -1 := by
    have h := miuraCartesianGardnerBracket_antisymm a ha n n hn hn
      (ContinuousLinearMap.snd ℂ ℂ ℂ) (ContinuousLinearMap.fst ℂ ℂ ℂ)
    change l2GardnerBracket (miuraCartesianY n) (miuraCartesianX n) (scalarInclusion a) =
      -l2GardnerBracket (miuraCartesianX n) (miuraCartesianY n) (scalarInclusion a) at h
    rwa [hXY] at h
  constructor
  · rw [miuraCartesianJacobian_eval _ har n hn,
      ← l2GardnerBracket_pair (miuraL2CartesianCoordinates n) (miuraCartesianX n) _ hf]
    change (l2GardnerBracket (miuraCartesianX n) (miuraCartesianX n) _,
      l2GardnerBracket (miuraCartesianY n) (miuraCartesianX n) _) = _
    rw [hXX,hYX]
  · rw [miuraCartesianJacobian_eval _ har n hn,
      ← l2GardnerBracket_pair (miuraL2CartesianCoordinates n) (miuraCartesianY n) _ hf]
    change (l2GardnerBracket (miuraCartesianX n) (miuraCartesianY n) _,
      l2GardnerBracket (miuraCartesianY n) (miuraCartesianY n) _) = _
    rw [hXY,hYY]

end NLS.MKdV
