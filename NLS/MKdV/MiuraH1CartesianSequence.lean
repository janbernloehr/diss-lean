import NLS.MKdV.MiuraSobolevCartesianActions
import NLS.MKdV.MiuraActionFlowGroup

/-! # The full native Cartesian map on the original physical H¹ space

The coefficient-preserving original H¹ equivalence gives a full Banach
analytic map into the weighted Hilbert pair of order three halves. Every
selected radius is the independently defined physical Hill-contour action.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraH1CartesianSequence (a : ScalarDomain 2) : MiuraSobolevCartesianTarget 1 :=
  miuraSobolevCartesianSequence 1 (miuraH1SobolevEquiv a)

theorem analyticAt_miuraH1CartesianSequence (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ miuraH1CartesianSequence a :=
  (analyticAt_miuraSobolevCartesianSequence 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha)).comp
    (miuraH1SobolevEquiv.toContinuousLinearEquiv.analyticAt a)

/-- The native H¹ construction leaves every original selected pair unchanged. -/
theorem miuraH1CartesianSequence_positive (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraH1CartesianSequence a).1.val n,(miuraH1CartesianSequence a).2.val n) =
      miuraL2CartesianCoordinates n (scalarInclusion a) := by
  have h := miuraSobolevCartesianSequence_positive 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) n hn
  have he : hierarchySobolevJetL2 1 0 (Nat.zero_le 1) (miuraH1SobolevEquiv a) = scalarInclusion a := by
    ext j
    rw [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraH1SobolevEquiv_apply,scalarInclusion_apply]
  rw [he] at h
  exact h

/-- Exact independent physical action radii hold in the full original H¹
Cartesian map, including any closed selected action. -/
theorem miuraH1CartesianSequence_physical_radius (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraH1CartesianSequence a).1.val n)^2+((miuraH1CartesianSequence a).2.val n)^2 =
      2*miuraMKdVAction a ha n := by
  have h := congrArg (fun z : ℂ × ℂ => z.1^2+z.2^2) (miuraH1CartesianSequence_positive a ha n hn)
  exact h.trans (miuraL2CartesianCoordinates_physical_H1_radius a ha n hn)

theorem miuraCartesianWeight_one (n : ℤ) : miuraCartesianWeight 1 n = Weight.sobolev (3/2) n := by
  unfold miuraCartesianWeight
  norm_num

end NLS.MKdV
