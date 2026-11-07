import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryAnalytic
import NLS.ZakharovShabat.SourcePhaseCompatibility

/-! Algebraic simplicity of EVERY actual original auxiliary root at real
source potentials. Phase conjugation retains the finite central block. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every canonical auxiliary coordinate has actual operator algebraic
multiplicity one at real type, including central and collapsed-gap indices. -/
theorem canonicalAuxiliaryPeriodOneRoots_algebraicMultiplicity_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    b.auxiliaryAlgebraicMultiplicity hp (auxiliaryPeriodOnePotential hp hp1 φ).val
      (auxiliaryPeriodOnePotential hp hp1 φ).property
      (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n) = 1 := by
  rw [BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
  change b.algebraicMultiplicity hp (auxiliaryPeriodOneDirichletPotential hp hp1 φ).val
    (auxiliaryPeriodOneDirichletPotential hp hp1 φ).property
    (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n) = 1
  rw [auxiliaryPeriodOneDirichletPotential_eq_sourcePhase,
    canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]
  exact canonicalPeriodOneBoundaryRoots_algebraicMultiplicity_eq_one_of_realType
    hp hp1 b (sourcePhase φ) (isRealType_sourcePhase φ hφ) n

/-- Any zero of the actual auxiliary characteristic is simple at real
source potentials; there is no prescribed-index or high-frequency premise. -/
theorem analyticOrderAt_auxiliaryPeriodOneCharacteristic_eq_one_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : auxiliaryPeriodOneCharacteristic hp hp1 b φ z = 0) :
    analyticOrderAt (auxiliaryPeriodOneCharacteristic hp hp1 b φ) z = 1 := by
  obtain ⟨n,hn⟩ := (canonicalAuxiliaryPeriodOneRoots_exhaustive hp hp1 b φ z).mp
    ((auxiliaryPeriodOneCharacteristic_eq_zero_iff hp hp1 b φ z).mp hz)
  rw [analyticOrderAt_auxiliaryPeriodOneCharacteristic,← hn,
    canonicalAuxiliaryPeriodOneRoots_algebraicMultiplicity_eq_one_of_realType hp hp1 b φ hφ n]
  rfl

end NLS.ZakharovShabat
