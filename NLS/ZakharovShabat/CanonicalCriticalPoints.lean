import NLS.ZakharovShabat.OrderedCriticalUniqueness
import NLS.ZakharovShabat.RealDiscriminantCritical

/-!
# Canonical ordered critical-point coordinates

Existence supplies one ordered complete labeling. Uniqueness makes its
coordinates independent of every auxiliary central cutoff and enumeration.
These coordinates retain the exact multiplicities and derivative product.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One admissible cutoff witnessing the canonical critical sequence. -/
def canonicalCriticalCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℕ :=
  (exists_ordered_criticalPointLabeling_memℓp hp hp1 φ hφ).choose

/-- The uniquely determined lexicographically ordered critical points. -/
def canonicalCriticalPoints (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℤ → ℂ :=
  (exists_ordered_criticalPointLabeling_memℓp hp hp1 φ hφ).choose_spec.choose

/-- The canonical sequence has a valid cutoff, is ordered, and has lp displacement. -/
theorem canonicalCriticalPoints_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) :
    CriticalPointLabeling hp hp1 φ hφ (canonicalCriticalCutoff hp hp1 φ hφ)
      (canonicalCriticalPoints hp hp1 φ hφ) ∧
    Monotone (fun n => complexLexKey (canonicalCriticalPoints hp hp1 φ hφ n)) ∧
    Memℓp (fun n => canonicalCriticalPoints hp hp1 φ hφ n-(Real.pi : ℂ)*n) p :=
  (exists_ordered_criticalPointLabeling_memℓp hp hp1 φ hφ).choose_spec.choose_spec

/-- Every ordered complete labeling agrees with the canonical coordinates, irrespective of cutoff. -/
theorem CriticalPointLabeling.eq_canonicalCriticalPoints {hp : p ≠ ⊤} {hp1 : 1 < p}
    {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0} {N : ℕ} {ξ : ℤ → ℂ}
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (hs : Monotone (fun n => complexLexKey (ξ n))) :
    ξ = canonicalCriticalPoints hp hp1 φ hφ :=
  h.ordered_unique (canonicalCriticalPoints_spec hp hp1 φ hφ).1 hs
    (canonicalCriticalPoints_spec hp hp1 φ hφ).2.1

/-- The canonical coordinates enumerate all and only critical points. -/
theorem canonicalCriticalPoints_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    deriv (canonicalDiscriminant hp φ) z = 0 ↔ ∃ n, canonicalCriticalPoints hp hp1 φ hφ n = z :=
  (canonicalCriticalPoints_spec hp hp1 φ hφ).1.exhaustive z

/-- Every canonical coordinate is an actual critical point. -/
theorem canonicalCriticalPoints_is_critical (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    deriv (canonicalDiscriminant hp φ) (canonicalCriticalPoints hp hp1 φ hφ n) = 0 :=
  (canonicalCriticalPoints_spec hp hp1 φ hφ).1.is_critical n

/-- Repetitions in the canonical sequence are exactly the derivative's analytic multiplicities. -/
theorem canonicalCriticalPoints_multiplicity (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (∑ᶠ n : ℤ, if canonicalCriticalPoints hp hp1 φ hφ n = z then (1 : ℕ) else 0) =
      analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z :=
  (canonicalCriticalPoints_spec hp hp1 φ hφ).1.multiplicity z

/-- The canonical sequence has the source's global lexicographic order. -/
theorem monotone_canonicalCriticalPoints (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) :
    Monotone (fun n => complexLexKey (canonicalCriticalPoints hp hp1 φ hφ n)) :=
  (canonicalCriticalPoints_spec hp hp1 φ hφ).2.1

/-- The canonical displacement is an element of the original coefficient space. -/
def canonicalCriticalDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : Coeff p :=
  ⟨_,(canonicalCriticalPoints_spec hp hp1 φ hφ).2.2⟩

@[simp] theorem canonicalCriticalDisplacement_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalCriticalDisplacement hp hp1 φ hφ n = canonicalCriticalPoints hp hp1 φ hφ n-(Real.pi : ℂ)*n := rfl

/-- The canonical ordered roots give the exact derivative product. -/
theorem discriminant_derivative_eq_canonicalCriticalProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    deriv (canonicalDiscriminant hp φ) z = entireSingleSpectralProduct (canonicalCriticalPoints hp hp1 φ hφ) z :=
  ((canonicalCriticalPoints_spec hp hp1 φ hφ).1.product_eq_derivative
    (canonicalCriticalPoints_spec hp hp1 φ hφ).2.2 z).symm

/-- At real-type potentials every canonical critical coordinate is real. -/
theorem canonicalCriticalPoints_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    (canonicalCriticalPoints hp hp1 φ hφ n).im = 0 :=
  discriminant_critical_im_eq_zero_of_realType hp hp1 φ hφ hreal
    (canonicalCriticalPoints_is_critical hp hp1 φ hφ n)

end NLS.ZakharovShabat
