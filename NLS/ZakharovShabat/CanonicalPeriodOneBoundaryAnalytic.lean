import NLS.ZakharovShabat.SourceSpectralClusters
import NLS.ZakharovShabat.BoundarySimpleBranchAnalytic

/-!
# Simple analytic source Dirichlet and Neumann coordinates

Real source interlacing separates every two indexed boundary coordinates.
The complete canonical multiplicity formula then gives algebraic multiplicity
one at every index, including central indices and collapsed periodic gaps.
Continuity and the local rank-one contour trace prove source analyticity.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real parts of either ordinary source boundary sequence are strictly
increasing at every real-type source. -/
theorem strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    StrictMono (fun n : ℤ => (canonicalPeriodOneBoundaryRoots hp hp1 b φ n).re) := by
  have hmem (n : ℤ) : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ∈
      sourceSpectralCluster hp hp1 φ n := by
    cases b with
    | dirichlet => exact Or.inr (Or.inr (Or.inl rfl))
    | neumann => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  intro i j hij
  exact sourceSpectralCluster_re_lt_of_lt hp hp1 φ hφ hij (hmem i) (hmem j)

/-- Distinct indices give distinct roots, even when a surrounding periodic
gap collapses. -/
theorem injective_canonicalPeriodOneBoundaryRoots_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Function.Injective (canonicalPeriodOneBoundaryRoots hp hp1 b φ) := by
  intro i j hij
  exact (strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType hp hp1 b φ hφ).injective
    (congrArg Complex.re hij)

/-- Every ordinary source boundary root has original algebraic multiplicity
one at real type, with no exclusion of central or collapsed gaps. -/
theorem canonicalPeriodOneBoundaryRoots_algebraicMultiplicity_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = 1 := by
  rw [← canonicalPeriodOneBoundaryRoots_multiplicity hp hp1 b φ]
  rw [finsum_eq_single _ n (by
    intro m hmn
    have hne : canonicalPeriodOneBoundaryRoots hp hp1 b φ m ≠
        canonicalPeriodOneBoundaryRoots hp hp1 b φ n := fun h =>
      hmn (injective_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hφ h)
    simp only [if_neg hne]), if_pos rfl]

/-- Every canonical ordinary source boundary coordinate is complex analytic
at every real-type source potential, including the finite central block. -/
theorem analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  let F := periodOneBoundaryPotential hp hp1
  have hA : AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) =>
      b.canonicalRoots hp hp1 ψ.val ψ.property n) (F φ) :=
    b.analyticAt_of_continuous_simple_spectral_branch hp _ (F φ)
      (continuousAt_canonicalBoundaryRoots_of_realType hp hp1 b (F φ)
        (isRealType_periodOneBoundaryPotential hp hp1 φ hφ) n)
      (fun ψ => b.canonicalRoots_mem_spectrum hp hp1 ψ.val ψ.property n)
      (canonicalPeriodOneBoundaryRoots_algebraicMultiplicity_eq_one_of_realType hp hp1 b φ hφ n)
  exact AnalyticAt.comp (g := fun ψ : dirichletSubspace (p := p) =>
    b.canonicalRoots hp hp1 ψ.val ψ.property n) (f := F) (x := φ) hA (F.analyticAt φ)

end NLS.ZakharovShabat
