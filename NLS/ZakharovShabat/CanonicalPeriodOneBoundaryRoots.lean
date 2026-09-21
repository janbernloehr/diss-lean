import NLS.ZakharovShabat.CanonicalBoundaryContinuity
import NLS.ZakharovShabat.CanonicalBoundaryFree
import NLS.ZakharovShabat.AuxiliaryReality

/-! # Canonical boundary coordinates on the original source space
The proved ordinary interval extension preserves real type. Its continuous
linear pullback therefore gives the source Dirichlet and Neumann coordinates
and their continuity under arbitrary complex perturbations, as in Lemma 9.1(ii).
-/

noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical ordinary boundary roots of a source period-one coefficient potential. -/
def canonicalPeriodOneBoundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) : ℤ → ℂ :=
  b.canonicalRoots hp hp1 (periodOneBoundaryPotential hp hp1 φ).val
    (periodOneBoundaryPotential hp hp1 φ).property

/-- The ordinary source interval extension preserves the Fourier real-type relation. -/
theorem isRealType_periodOneBoundaryPotential (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (periodOneBoundaryPotential hp hp1 φ).val :=
  BoundaryCondition.isRealType_intervalExtensionCLM .dirichlet hp1 hp _ hφ

/-- The source canonical coordinates exhaust the actual ordinary boundary spectrum. -/
theorem canonicalPeriodOneBoundaryRoots_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ) :
    z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property ↔
      ∃ n : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 b φ n = z :=
  b.canonicalRoots_exhaustive hp hp1 _ _ z

/-- Canonical source coordinates retain every original algebraic multiplicity. -/
theorem canonicalPeriodOneBoundaryRoots_multiplicity (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ) :
    (∑ᶠ n : ℤ, if canonicalPeriodOneBoundaryRoots hp hp1 b φ n = z then (1 : ℕ) else 0) =
      b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
        (periodOneBoundaryPotential hp hp1 φ).property z :=
  b.canonicalRoots_multiplicity hp hp1 _ _ z

/-- Both source characteristics have their literal canonical ordered product. -/
theorem periodOneBoundaryCharacteristic_eq_canonicalProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    periodOneBoundaryCharacteristic hp hp1 b φ =
      boundaryCharacteristicProduct (canonicalPeriodOneBoundaryRoots hp hp1 b φ) :=
  b.characteristic_eq_canonicalProduct hp hp1 _ _

/-- At zero source potential both canonical sequences are the signed free lattice. -/
@[simp] theorem canonicalPeriodOneBoundaryRoots_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 b (0 : CoeffPair p) n = (Real.pi : ℂ)*n := by
  simp only [canonicalPeriodOneBoundaryRoots,map_zero]
  exact b.canonicalRoots_zero hp hp1 n

/-- Every canonical source boundary root is real at a source real-type potential. -/
theorem canonicalPeriodOneBoundaryRoots_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n).im = 0 :=
  b.canonicalRoots_im_eq_zero hp hp1 _ _ (isRealType_periodOneBoundaryPotential hp hp1 φ hφ) n

/-- Ordinary Lemma 9.1(ii): every source boundary coordinate is continuous at each real-type potential. -/
theorem continuousAt_canonicalPeriodOneBoundaryRoots_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ :=
  (continuousAt_canonicalBoundaryRoots_of_realType hp hp1 b (periodOneBoundaryPotential hp hp1 φ)
    (isRealType_periodOneBoundaryPotential hp hp1 φ hφ) n).comp (periodOneBoundaryPotential hp hp1).continuous.continuousAt

/-- Source displacements of fixed coordinates are also continuous at every real-type potential. -/
theorem continuousAt_canonicalPeriodOneBoundaryDisplacement_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n-(Real.pi : ℂ)*n) φ :=
  (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hφ n).sub continuousAt_const

/-- Away from a finite central block, source canonical roots are analytic at arbitrary complex potentials. -/
theorem exists_analyticAt_distant_canonicalPeriodOneBoundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) : ∃ N : ℕ, 0 < N ∧ ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
      AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N,hN,hA⟩ := exists_analyticAt_distant_canonicalBoundaryRoots hp hp1 (F φ)
  refine ⟨N,hN,fun b n hn => ?_⟩
  exact AnalyticAt.comp (g := fun ψ : dirichletSubspace (p := p) => b.canonicalRoots hp hp1 ψ.val ψ.property n)
    (f := F) (x := φ) (hA b n hn) (F.analyticAt φ)

end NLS.ZakharovShabat
