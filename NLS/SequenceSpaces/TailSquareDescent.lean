import NLS.SequenceSpaces.MixedSquare
import NLS.SequenceSpaces.ComplexSignInvariance
import NLS.ComplexAnalysis.OpenMapDescent

/-! # Continuous descent through squared tail coordinates

An invariant continuous map descends to the open mixed-coordinate image.
The definition is independent of all tail square-root choices, recovers
the original function, and preserves uniform bounds. Analytic regularity
on the descended domain is not asserted here.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [Nonempty F]

/-- The function of finite head values and squared tail coordinates. -/
def tailSquareDescent (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (V : Set (Coeff p × Coeff p)) : (Coeff q × Coeff q) → F :=
  ComplexAnalysis.openMapDescent (pairMixedSquare S) f V

omit [Nonempty F] in
/-- Tail sign invariance identifies every fiber of the mixed coordinate map. -/
theorem eq_of_pairMixedSquare_eq (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (V : Set (Coeff p × Coeff p))
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z w : Coeff p × Coeff p) (hz : z ∈ V)
    (he : pairMixedSquare (q := q) S z = pairMixedSquare S w) : f w = f z := by
  obtain ⟨hh,hs⟩ := (pairMixedSquare_eq_iff S z w).mp he
  exact eq_of_coordinate_squares_of_eq_head f S V hinv z w hz hh hs

/-- Descent exactly recovers the lifted function at every source point. -/
theorem tailSquareDescent_apply (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (V : Set (Coeff p × Coeff p))
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) :
    tailSquareDescent (q := q) S f V (pairMixedSquare S z) = f z :=
  ComplexAnalysis.openMapDescent_apply _ f V
    (fun z hz w _ he => (eq_of_pairMixedSquare_eq S f V hinv z w hz he).symm) z hz

/-- Every pointwise property, in particular a uniform norm bound, passes
to the descended function on the entire mixed-coordinate image. -/
theorem tailSquareDescent_property (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (V : Set (Coeff p × Coeff p))
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (P : F → Prop) (hP : ∀ z ∈ V, P (f z)) :
    ∀ b ∈ pairMixedSquare (q := q) S '' V, P (tailSquareDescent S f V b) := by
  rintro _ ⟨z,hz,rfl⟩
  rw [tailSquareDescent_apply S f V hinv z hz]
  exact hP z hz

variable [TopologicalSpace F]

/-- The descended function is continuous in the half-exponent norm. -/
theorem continuousOn_tailSquareDescent (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : ContinuousOn f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z) :
    ContinuousOn (tailSquareDescent (q := q) S f V) (pairMixedSquare S '' V) :=
  ComplexAnalysis.continuousOn_openMapDescent _ f V
    (continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn)
    (isOpenMap_pairMixedSquare hp S) hV hf
    (fun z hz w _ he => (eq_of_pairMixedSquare_eq S f V hinv z w hz he).symm)

omit [TopologicalSpace F] in
/-- A descended function with the recovery identity is unique on the image. -/
theorem eqOn_tailSquareDescent (S : Finset ℤ) (f : (Coeff p × Coeff p) → F)
    (V : Set (Coeff p × Coeff p))
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (g : (Coeff q × Coeff q) → F) (hg : ∀ z ∈ V, g (pairMixedSquare S z) = f z) :
    EqOn g (tailSquareDescent S f V) (pairMixedSquare S '' V) :=
  ComplexAnalysis.eqOn_openMapDescent _ f V
    (fun z hz w _ he => (eq_of_pairMixedSquare_eq S f V hinv z w hz he).symm) g hg

end NLS.Coeff
