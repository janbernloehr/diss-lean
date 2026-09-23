import NLS.ZakharovShabat.AuxiliaryRootSpaces
import NLS.ZakharovShabat.AuxiliaryReality
import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryRoots

/-! # Canonical coordinates of the actual auxiliary boundary restrictions
The auxiliary pencil is conjugate to the ordinary restricted pencil after
rotating its potential. Its signed root sequence therefore inherits the exact
actual spectrum, multiplicities, free values, and real-type continuity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The conjugated ordinary potential of the Neumann-reflected source input. -/
def auxiliaryPeriodOneDirichletPotential (hp : p ≠ ⊤) (hp1 : 1 < p) :
    CoeffPair p →L[ℂ] dirichletSubspace (p := p) :=
  (auxiliaryPotentialToDirichlet (p := p)).comp (auxiliaryPeriodOnePotential hp hp1)

/-- Canonical signed roots of the actual auxiliary Dirichlet or Neumann restriction. -/
def canonicalAuxiliaryPeriodOneRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) : ℤ → ℂ :=
  b.canonicalRoots hp hp1 (auxiliaryPeriodOneDirichletPotential hp hp1 φ).val
    (auxiliaryPeriodOneDirichletPotential hp hp1 φ).property

/-- Canonical starred coordinates enumerate the actual auxiliary spectrum. -/
theorem canonicalAuxiliaryPeriodOneRoots_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    z ∈ b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 φ).val
      (auxiliaryPeriodOnePotential hp hp1 φ).property ↔
      ∃ n : ℤ, canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n = z := by
  rw [b.auxiliarySpectrum_eq]
  exact b.canonicalRoots_exhaustive hp hp1 _ _ z

/-- The auxiliary root's original generalized multiplicity equals its signed-coordinate count. -/
theorem canonicalAuxiliaryPeriodOneRoots_multiplicity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    (∑ᶠ n : ℤ, if canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n = z then (1 : ℕ) else 0) =
      b.auxiliaryAlgebraicMultiplicity hp (auxiliaryPeriodOnePotential hp hp1 φ).val
        (auxiliaryPeriodOnePotential hp hp1 φ).property z := by
  rw [b.auxiliaryAlgebraicMultiplicity_eq]
  exact b.canonicalRoots_multiplicity hp hp1 _ _ z

/-- Both canonical starred sequences have the exact signed free lattice. -/
@[simp] theorem canonicalAuxiliaryPeriodOneRoots_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) :
    canonicalAuxiliaryPeriodOneRoots hp hp1 b (0 : CoeffPair p) n = (Real.pi : ℂ)*n := by
  simp only [canonicalAuxiliaryPeriodOneRoots, map_zero]
  exact b.canonicalRoots_zero hp hp1 n

/-- The phase-rotated source potential remains real type. -/
theorem isRealType_auxiliaryPeriodOneDirichletPotential (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (auxiliaryPeriodOneDirichletPotential hp hp1 φ).val :=
  (isRealType_auxiliaryPeriodOnePotential hp hp1 φ hφ).auxiliaryPotential

/-- Every canonical starred root is real for a real-type source potential. -/
theorem canonicalAuxiliaryPeriodOneRoots_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n).im = 0 :=
  b.canonicalRoots_im_eq_zero hp hp1 _ _ (isRealType_auxiliaryPeriodOneDirichletPotential hp hp1 φ hφ) n

/-- Each starred source coordinate is continuous at every real-type source potential. -/
theorem continuousAt_canonicalAuxiliaryPeriodOneRoots_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ContinuousAt (fun ψ : CoeffPair p => canonicalAuxiliaryPeriodOneRoots hp hp1 b ψ n) φ :=
  (continuousAt_canonicalBoundaryRoots_of_realType hp hp1 b
    (auxiliaryPeriodOneDirichletPotential hp hp1 φ)
    (isRealType_auxiliaryPeriodOneDirichletPotential hp hp1 φ hφ) n).comp
    (auxiliaryPeriodOneDirichletPotential hp hp1).continuous.continuousAt

end NLS.ZakharovShabat
