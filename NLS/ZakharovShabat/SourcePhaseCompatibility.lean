import NLS.ZakharovShabat.PeriodicPhaseConjugation
import NLS.ZakharovShabat.CanonicalAuxiliaryBoundaryRoots
import NLS.ZakharovShabat.AuxiliaryBoundaryCharacteristic
import NLS.ZakharovShabat.PeriodOneBoundaryAsymptotics
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # The source phase rotation and period-one constructions

The phase rotation is made on the original component-sum coefficient space.
It commutes with period doubling, and turns the Neumann reflection used for
starred boundary problems into the ordinary Dirichlet reflection.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Rotate the two original period-one source coefficients by opposite phases. -/
def sourcePhase : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((auxiliaryPotential (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourcePhase_fst (φ : CoeffPair p) :
    (sourcePhase φ).fst = Complex.I • φ.fst := rfl

@[simp] theorem sourcePhase_snd (φ : CoeffPair p) :
    (sourcePhase φ).snd = -Complex.I • φ.snd := rfl

/-- The phase rotation commutes with the original period-one embedding. -/
theorem periodOnePotential_sourcePhase (φ : CoeffPair p) :
    periodOnePotential (sourcePhase φ) = auxiliaryPotential (periodOnePotential φ) := by
  apply Prod.ext
  · change Coeff.periodDouble (Complex.I • φ.fst) = Complex.I • Coeff.periodDouble φ.fst
    exact map_smul Coeff.periodDouble Complex.I φ.fst
  · change Coeff.periodDouble (-Complex.I • φ.snd) = -Complex.I • Coeff.periodDouble φ.snd
    exact map_smul Coeff.periodDouble (-Complex.I) φ.snd

/-- Rotating the Neumann-reflected source gives the Dirichlet-reflected rotated source. -/
theorem auxiliaryPotential_intervalExtension_neumann (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : PairSpace p) :
    auxiliaryPotential (BoundaryCondition.intervalExtensionCLM .neumann hp1 hp a) =
      BoundaryCondition.intervalExtensionCLM .dirichlet hp1 hp (auxiliaryPotential a) := by
  have hA : BoundaryCondition.intervalAmplitudeCLM .dirichlet hp1 hp (auxiliaryPotential a) =
      -Complex.I • BoundaryCondition.intervalAmplitudeCLM .neumann hp1 hp a := by
    simp [BoundaryCondition.intervalAmplitudeCLM, BoundaryCondition.extensionSign,
      auxiliaryPotential_apply, map_smul, smul_add]
  apply Prod.ext
  · have hr := congrArg Coeff.reflection hA
    rw [map_smul] at hr
    simpa only [auxiliaryPotential_apply, BoundaryCondition.intervalExtensionCLM_fst,
      BoundaryCondition.extensionSign, one_smul, neg_one_smul, smul_neg, neg_smul] using hr.symm
  · simp only [auxiliaryPotential_apply, BoundaryCondition.intervalExtensionCLM_snd]
    exact hA.symm

/-- The actual starred source parameter is the ordinary source parameter at the rotated input. -/
theorem auxiliaryPeriodOneDirichletPotential_eq_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    auxiliaryPeriodOneDirichletPotential hp hp1 φ =
      periodOneBoundaryPotential hp hp1 (sourcePhase φ) := by
  apply Subtype.ext
  change auxiliaryPotential (BoundaryCondition.intervalExtensionCLM .neumann hp1 hp (CoeffPair.toMax p φ)) =
    BoundaryCondition.intervalExtensionCLM .dirichlet hp1 hp
      (auxiliaryPotential (CoeffPair.toMax p φ))
  exact auxiliaryPotential_intervalExtension_neumann hp hp1 _

/-- Every starred signed coordinate is an ordinary coordinate of the phase-rotated source. -/
theorem canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    canonicalAuxiliaryPeriodOneRoots hp hp1 b φ =
      canonicalPeriodOneBoundaryRoots hp hp1 b (sourcePhase φ) := by
  simpa only [canonicalAuxiliaryPeriodOneRoots, canonicalPeriodOneBoundaryRoots] using
    congrArg (fun ψ : dirichletSubspace (p := p) =>
      b.canonicalRoots hp hp1 ψ.val ψ.property)
      (auxiliaryPeriodOneDirichletPotential_eq_sourcePhase hp hp1 φ)

/-- The normalized starred characteristic is the ordinary characteristic of the rotated source. -/
theorem auxiliaryPeriodOneCharacteristic_eq_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    auxiliaryPeriodOneCharacteristic hp hp1 b φ =
      periodOneBoundaryCharacteristic hp hp1 b (sourcePhase φ) := by
  funext z
  exact congrArg (fun ψ : dirichletSubspace (p := p) =>
    b.characteristic hp ψ.val ψ.property z)
    (auxiliaryPeriodOneDirichletPotential_eq_sourcePhase hp hp1 φ)

/-- The source phase rotation preserves the real-type relation. -/
theorem isRealType_sourcePhase (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourcePhase φ)) := by
  change IsRealType (auxiliaryPotential (CoeffPair.toMax p φ))
  exact hφ.auxiliaryPotential

/-- The rotated source has precisely the original periodic spectrum. -/
theorem periodicSpectrum_periodOne_sourcePhase (hp : p ≠ ⊤) (φ : CoeffPair p) :
    periodicSpectrum hp (periodOnePotential (sourcePhase φ)) =
      periodicSpectrum hp (periodOnePotential φ) := by
  rw [periodOnePotential_sourcePhase, periodicSpectrum_auxiliaryPotential]

/-- Original periodic algebraic multiplicities survive the source rotation. -/
theorem periodicAlgebraicMultiplicity_periodOne_sourcePhase (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential (sourcePhase φ)) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ) z := by
  rw [periodOnePotential_sourcePhase, periodicAlgebraicMultiplicity_auxiliaryPotential]

end NLS.ZakharovShabat
