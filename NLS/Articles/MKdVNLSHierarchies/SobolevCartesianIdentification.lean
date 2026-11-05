import NLS.MKdV.MiuraH1CartesianSequence

/-! # Full native Sobolev Cartesian representatives of the physical actions

The original Cartesian family is Banach analytic H^s -> h^(s+1/2) at every
integer s>=0, with the entire actual weighted action sequence as quadratic
radii. Original H¹ specialization retains the independent Hill actions.
This does not supply Gardner canonicity or an independent inverse chart.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Full native complex Banach analyticity at every integer Sobolev order,
with no selected open-gap or nonzero-mean condition. -/
theorem native_cartesian_allSobolev_analytic (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ (miuraSobolevCartesianSequence s) a :=
  analyticAt_miuraSobolevCartesianSequence s a ha

/-- Every positive native coordinate is the unchanged actual selected pair. -/
theorem native_cartesian_allSobolev_coordinates (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraSobolevCartesianSequence s a).1.val n,(miuraSobolevCartesianSequence s a).2.val n) =
      miuraL2CartesianCoordinates n (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) :=
  miuraSobolevCartesianSequence_positive s a ha n hn

/-- Native weighted half-radius squares recover the entire actual action
sequence, with its full order 2*s+1 weighted l1 topology. -/
theorem native_cartesian_allSobolev_action_sequence (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraSobolevCartesianActions s (miuraSobolevCartesianSequence s a) = miuraSobolevActionSequence s a :=
  miuraSobolevCartesianActions_sequence_eq s a ha

/-- The original physical H¹ space has a full Banach analytic Cartesian
map into the native Hilbert pair of order three halves. -/
theorem physical_cartesian_original_H1_Banach_analytic (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ miuraH1CartesianSequence a :=
  analyticAt_miuraH1CartesianSequence a ha

/-- The full native original-H¹ map retains the independent physical
Hill-contour action radius, including each collapsed selected action. -/
theorem physical_cartesian_original_H1_native_radius (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraH1CartesianSequence a).1.val n)^2+((miuraH1CartesianSequence a).2.val n)^2 =
      2*miuraMKdVAction a ha n := miuraH1CartesianSequence_physical_radius a ha n hn

end NLS.Articles.MKdVNLSHierarchies
