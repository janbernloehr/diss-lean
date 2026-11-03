import NLS.MKdV.MiuraCartesianClosedAnnihilator

/-! # Every modal coefficient of a Cartesian Jacobian annihilator

At an open mode an annihilator is radial. At a closed mode stationary
equivariance and the actual canonical plane kill both coefficients.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianInsert (n : ℕ) (v : ℂ × ℂ) : MiuraPositiveCartesianTarget :=
  WeightedCoeff.positiveCartesianInsert (Weight.sobolev (1/2)) 2 n v

def miuraCartesianCotangentX (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ) (n : ℕ) : ℂ :=
  L (miuraCartesianInsert n (1,0))

def miuraCartesianCotangentY (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ) (n : ℕ) : ℂ :=
  L (miuraCartesianInsert n (0,1))

theorem miuraCartesianCotangent_insert (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (n : ℕ) (hn : 1 ≤ n) (v : ℂ × ℂ) :
    L (miuraCartesianInsert n v) = miuraCartesianCotangentX L n*v.1+miuraCartesianCotangentY L n*v.2 :=
  WeightedCoeff.cotangent_positiveCartesianInsert _ _ L n (by omega) v

theorem miuraCartesianCotangent_actionVector (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (n : ℕ) (hn : 1 ≤ n) (z : MiuraPositiveCartesianTarget) :
    L (miuraCartesianActionVector n z) =
      miuraCartesianCotangentX L n*(miuraPositiveCartesianEval n z).2-
        miuraCartesianCotangentY L n*(miuraPositiveCartesianEval n z).1 := by
  change L (WeightedCoeff.positiveCartesianActionVector (Weight.sobolev (1/2)) 2 (n : ℤ) z) = _
  rw [WeightedCoeff.positiveCartesianActionVector_eq_insert _ _ n (by omega)]
  change L (miuraCartesianInsert n ((miuraPositiveCartesianEval n z).2,-(miuraPositiveCartesianEval n z).1)) = _
  rw [miuraCartesianCotangent_insert L n hn]
  ring

theorem miuraCartesian_annihilator_radial (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    miuraCartesianCotangentX L n*miuraCartesianY n (scalarInclusion a)-
      miuraCartesianCotangentY L n*miuraCartesianX n (scalarInclusion a) = 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have h := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ =>
    Q (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))) hL
  change L (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))) = 0 at h
  rw [miuraCartesianJacobian_Gardner_action a ha n hn,
    miuraCartesianCotangent_actionVector L n hn,miuraPositiveCartesianMap_positive _ har n hn] at h
  exact h

theorem miuraCartesian_annihilator_closed_coefficients (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) (L : MiuraPositiveCartesianTarget →L[ℂ] ℂ)
    (hL : L.comp (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)) = 0) :
    miuraCartesianCotangentX L n = 0 ∧ miuraCartesianCotangentY L n = 0 := by
  have hQ := miuraCartesian_closed_annihilator_rotation a ha n hn hzero L hL
  have hown := miuraCartesianJacobian_own_Gardner_pairs a ha n hn
  have hx := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q
    (l2GardnerDirection (miuraCartesianX n) (scalarInclusion a))) hQ
  have hy := congrArg (fun Q : Coeff 2 →L[ℂ] ℂ => Q
    (l2GardnerDirection (miuraCartesianY n) (scalarInclusion a))) hQ
  change L (miuraCartesianActionVector n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianX n) (scalarInclusion a)))) = 0 at hx
  change L (miuraCartesianActionVector n (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
    (l2GardnerDirection (miuraCartesianY n) (scalarInclusion a)))) = 0 at hy
  rw [miuraCartesianCotangent_actionVector L n hn,hown.1] at hx
  rw [miuraCartesianCotangent_actionVector L n hn,hown.2] at hy
  exact ⟨by simpa using hx,by simpa using hy⟩

end NLS.MKdV
