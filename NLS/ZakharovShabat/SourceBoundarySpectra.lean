import NLS.ZakharovShabat.SourceLemma4_4
import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryRoots

/-!
# The original restricted spectra following Lemma 4.4

The spectrum is the complement of bijectivity for the actual original-norm
boundary pencil. Continuous changes of base and domain norms identify it with
the previously constructed boundary spectrum. In particular the canonical
source labels exhaust this spectrum. This does not assert the disputed
all-exponent height in Theorem 1.4 or a new original-norm Riesz rank formula.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Spectrum of the actual restricted operator in the original norms. -/
def sourceBoundarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) : Set ℂ :=
  (sourceBoundaryResolventSet b hp φ hφ)ᶜ

/-- Equivalent base and domain norms preserve the full restricted spectrum. -/
theorem sourceBoundarySpectrum_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    sourceBoundarySpectrum b hp φ hφ = b.spectrum hp (CoeffPair.toMax p φ) hφ := by
  unfold sourceBoundarySpectrum BoundaryCondition.spectrum
  rw [sourceBoundaryResolventSet_eq]

/-- The spectrum of each original-norm restriction is closed. -/
theorem isClosed_sourceBoundarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    IsClosed (sourceBoundarySpectrum b hp φ hφ) := by
  rw [sourceBoundarySpectrum_eq]
  exact b.isClosed_spectrum hp _ hφ

/-- The spectrum of each original-norm restriction is discrete. -/
theorem discreteTopology_sourceBoundarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    DiscreteTopology (sourceBoundarySpectrum b hp φ hφ) := by
  rw [sourceBoundarySpectrum_eq]
  exact b.discreteTopology_spectrum hp _ hφ

/-- Bounded regions contain only finitely many boundary spectral points. -/
theorem finite_sourceBoundarySpectrum_inter (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet)
    {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (sourceBoundarySpectrum b hp φ hφ ∩ K) := by
  rw [sourceBoundarySpectrum_eq]
  exact b.finite_spectrum_inter_of_isBounded hp _ hφ hK

/-- The original periodic spectrum is the union of the two actual restrictions. -/
theorem sourcePeriodicSpectrum_eq_sourceBoundary_union (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) :
    (sourceResolventSet hp φ)ᶜ = sourceBoundarySpectrum .dirichlet hp φ hφ ∪
      sourceBoundarySpectrum .neumann hp φ hφ := by
  rw [sourceResolventSet_eq, sourceBoundarySpectrum_eq, sourceBoundarySpectrum_eq]
  exact periodicSpectrum_eq_boundary_union hp _ hφ

/-- The completed original interval extension gives the existing source spectrum. -/
theorem sourceBoundarySpectrum_reflected (b : BoundaryCondition) (hp1 : 1 < p)
    (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceBoundarySpectrum b hp (sourceReflectedPotential hp1 hp φ)
      (sourceReflectedPotential_mem hp1 hp φ) =
    b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property := by
  rw [sourceBoundarySpectrum_eq]
  congr 1
  exact toMax_sourceReflectedPotential hp1 hp φ

/-- The canonical labels exhaust the actual original-norm restricted spectrum. -/
theorem mem_sourceBoundarySpectrum_reflected_iff (b : BoundaryCondition) (hp1 : 1 < p)
    (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) :
    z ∈ sourceBoundarySpectrum b hp (sourceReflectedPotential hp1 hp φ)
      (sourceReflectedPotential_mem hp1 hp φ) ↔
      ∃ n : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 b φ n = z := by
  rw [sourceBoundarySpectrum_reflected]
  exact canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ z

end NLS.ZakharovShabat
