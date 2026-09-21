import NLS.ZakharovShabat.OrderedBoundaryUniqueness
import NLS.ZakharovShabat.BoundaryCharacteristicOrders
import NLS.ZakharovShabat.RealType

/-!
# Canonical ordered Dirichlet and Neumann root coordinates
Ordered complete labelings are unique across cutoffs. Their canonical
coordinates retain all original algebraic multiplicities, lp displacements,
and the characteristic product. At real-type potentials every root is real.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BoundaryCondition
variable (b : BoundaryCondition)

/-- An admissible cutoff witnessing the canonical boundary sequence. -/
def canonicalRootCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : ℕ :=
  (exists_ordered_boundaryRootLabeling hp hp1 ⟨φ,hφ⟩ b).choose

/-- The unique lexicographically ordered complete boundary root sequence. -/
def canonicalRoots (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : ℤ → ℂ :=
  (exists_ordered_boundaryRootLabeling hp hp1 ⟨φ,hφ⟩ b).choose_spec.choose

/-- The canonical sequence is a complete actual boundary labeling and has the source lexicographic order. -/
theorem canonicalRoots_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    BoundaryRootLabeling b hp φ hφ (b.canonicalRootCutoff hp hp1 φ hφ) (b.canonicalRoots hp hp1 φ hφ) ∧
      Monotone (fun n => complexLexKey (b.canonicalRoots hp hp1 φ hφ n)) :=
  (exists_ordered_boundaryRootLabeling hp hp1 ⟨φ,hφ⟩ b).choose_spec.choose_spec

/-- Canonical coordinates exhaust the actual boundary spectrum. -/
theorem canonicalRoots_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    z ∈ b.spectrum hp φ hφ ↔ ∃ n : ℤ, b.canonicalRoots hp hp1 φ hφ n = z :=
  (b.canonicalRoots_spec hp hp1 φ hφ).1.exhaustive z

/-- Every canonical boundary coordinate is an actual eigenvalue. -/
theorem canonicalRoots_mem_spectrum (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (n : ℤ) : b.canonicalRoots hp hp1 φ hφ n ∈ b.spectrum hp φ hφ :=
  (b.canonicalRoots_exhaustive hp hp1 φ hφ _).mpr ⟨n,rfl⟩

/-- Repeated canonical values have exactly their original boundary algebraic multiplicities. -/
theorem canonicalRoots_multiplicity (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    (∑ᶠ n : ℤ, if b.canonicalRoots hp hp1 φ hφ n = z then (1 : ℕ) else 0) =
      b.algebraicMultiplicity hp φ hφ z :=
  (b.canonicalRoots_spec hp hp1 φ hφ).1.multiplicity z

/-- The canonical coordinates are globally ordered by real part and then imaginary part. -/
theorem monotone_canonicalRoots (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    Monotone (fun n => complexLexKey (b.canonicalRoots hp hp1 φ hφ n)) :=
  (b.canonicalRoots_spec hp hp1 φ hφ).2

/-- The full canonical displacement belongs to the original coefficient space. -/
def canonicalDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : Coeff p :=
  ⟨_,(b.canonicalRoots_spec hp hp1 φ hφ).1.displacement⟩

@[simp] theorem canonicalDisplacement_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (n : ℤ) :
    b.canonicalDisplacement hp hp1 φ hφ n = b.canonicalRoots hp hp1 φ hφ n-(Real.pi : ℂ)*n := rfl

/-- Canonical roots give the intrinsic characteristic with its original source normalization. -/
theorem characteristic_eq_canonicalProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) :
    b.characteristic hp φ hφ = boundaryCharacteristicProduct (b.canonicalRoots hp hp1 φ hφ) :=
  (b.canonicalRoots_spec hp hp1 φ hφ).1.product_eq_characteristic.symm

/-- The literal canonical cutoffs converge locally uniformly to the intrinsic boundary characteristic. -/
theorem tendstoLocallyUniformlyOn_canonicalProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) :
    TendstoLocallyUniformlyOn (fun N z => boundaryCharacteristicPartialProduct (b.canonicalRoots hp hp1 φ hφ) z N)
      (b.characteristic hp φ hφ) atTop univ := by
  rw [b.characteristic_eq_canonicalProduct hp hp1 φ hφ]
  exact tendstoLocallyUniformlyOn_boundaryCharacteristicProduct hp _ (b.canonicalRoots_spec hp hp1 φ hφ).1.displacement

/-- Every canonical coordinate is real at a real-type reflected potential. -/
theorem canonicalRoots_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (hreal : IsRealType φ) (n : ℤ) : (b.canonicalRoots hp hp1 φ hφ n).im = 0 :=
  periodicSpectrum_im_eq_zero_of_realType hp φ hreal _
    (b.spectrum_subset_periodic hp φ hφ (b.canonicalRoots_mem_spectrum hp hp1 φ hφ n))

end BoundaryCondition

/-- Every ordered complete boundary labeling equals the canonical sequence, regardless of cutoff. -/
theorem BoundaryRootLabeling.eq_canonicalRoots {b : BoundaryCondition} {hp : p ≠ ⊤} (hp1 : 1 < p)
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N ξ) (hs : Monotone (fun n => complexLexKey (ξ n))) :
    ξ = b.canonicalRoots hp hp1 φ hφ :=
  h.ordered_unique (b.canonicalRoots_spec hp hp1 φ hφ).1 hs (b.canonicalRoots_spec hp hp1 φ hφ).2

end NLS.ZakharovShabat
