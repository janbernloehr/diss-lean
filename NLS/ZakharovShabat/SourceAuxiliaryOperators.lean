import NLS.ZakharovShabat.SourceAuxiliarySpaces
import NLS.ZakharovShabat.SourceLemma4_4
import NLS.ZakharovShabat.AuxiliarySpectrum
import NLS.ZakharovShabat.AuxiliarySourceExtension
import NLS.ZakharovShabat.SourceLemma4_3Physical

/-!
# Auxiliary restricted operators in the original spaces

Both auxiliary restrictions use the same Neumann-reflected potential.
The original one-derivative domain is invariant under the actual operator.
The restricted pencil is formed as z times actual inclusion minus actual
operator; continuous changes of norms identify its full resolvent set and
spectrum with the existing auxiliary coefficient realization. This does not
assert Proposition 5.2's numerical height or original Riesz rank formulas.
-/

noncomputable section
open scoped ENNReal
open MeasureTheory Set
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both auxiliary restrictions use the same original Neumann-reflected potential. -/
def sourceAuxiliaryReflectedPotential (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) : CoeffPair p :=
  sourceBoundaryZeroWeightEquiv (sourceIntervalExtensionToBoundary .neumann hp1 hp φ).val

theorem sourceAuxiliaryReflectedPotential_mem (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceAuxiliaryReflectedPotential hp1 hp φ ∈ sourceBoundaryBaseSubspace .neumann :=
  (sourceBoundaryZeroWeightEquiv_mem .neumann _).mpr (sourceIntervalExtensionToBoundary .neumann hp1 hp φ).property

/-- At p=2 the completed reflected potential is the actual physical Neumann reflection. -/
theorem sourceAuxiliaryReflectedPotential_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    sourceAuxiliaryReflectedPotential (by norm_num) (by simp) (sourceUnitIntervalL2Coefficients φ hφ) =
      sourceNeumannPotentialCoefficients φ hφ :=
  sourceIntervalExtensionL2_ofFunction .neumann φ hφ

/-- The original source operator preserves either auxiliary boundary condition. -/
theorem sourceOperator_mem_auxiliarySourceSpace (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceWeightedAuxiliarySubspace b 1) :
    sourceOperator hp φ a ∈ auxiliarySourceSpace b := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm
    (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) ∈ auxiliarySpace b
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact operator_mem_auxiliary b hp _ hφ _ ha

/-- The actual auxiliary operator between the original weighted domain and base norms. -/
def sourceAuxiliaryOperator (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) :
    sourceWeightedAuxiliarySubspace (p := p) b 1 →L[ℂ] auxiliarySourceSpace (p := p) b :=
  ((sourceOperator hp φ).comp (sourceWeightedAuxiliarySubspace b 1).subtypeL).codRestrict _
    (fun a => sourceOperator_mem_auxiliarySourceSpace b hp φ hφ a.val a.property)

/-- The printed page-34 invariance for the actual completed interval potential. -/
theorem sourceAuxiliaryReflectedPotential_invariant (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : a ∈ sourceWeightedAuxiliarySubspace b 1) :
    sourceOperator hp (sourceAuxiliaryReflectedPotential hp1 hp φ) a ∈ auxiliarySourceSpace b :=
  sourceOperator_mem_auxiliarySourceSpace b hp _ (sourceAuxiliaryReflectedPotential_mem hp1 hp φ) a ha

/-- Domain inclusion retains the auxiliary condition in the original norms. -/
theorem sourceDomainInclusion_mem_auxiliary (b : BoundaryCondition)
    (a : WeightedCoeffPair (Weight.sobolev 1) p) (ha : a ∈ sourceWeightedAuxiliarySubspace b 1) :
    sourceDomainInclusion a ∈ auxiliarySourceSpace b := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm
    (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) ∈ auxiliarySpace b
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (inclusion_mem_auxiliary b _).mpr ha

/-- Actual inclusion for the original auxiliary restriction. -/
def sourceAuxiliaryInclusion (b : BoundaryCondition) :
    sourceWeightedAuxiliarySubspace (p := p) b 1 →L[ℂ] auxiliarySourceSpace (p := p) b :=
  ((sourceDomainInclusion (p := p)).comp (sourceWeightedAuxiliarySubspace b 1).subtypeL).codRestrict _
    (fun a => sourceDomainInclusion_mem_auxiliary b a.val a.property)

/-- The actual z-L pencil, formed from original auxiliary inclusion and operator. -/
def sourceAuxiliaryPencil (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    sourceWeightedAuxiliarySubspace (p := p) b 1 →L[ℂ] auxiliarySourceSpace (p := p) b :=
  z • sourceAuxiliaryInclusion b - sourceAuxiliaryOperator b hp φ hφ

/-- Equivalent norms on the actual auxiliary base subspace. -/
def sourceAuxiliaryBaseEquiv (b : BoundaryCondition) :
    auxiliarySourceSpace (p := p) b ≃L[ℂ] auxiliarySpace (p := p) b :=
  (CoeffPair.toMax p).ofSubmodule' (auxiliarySpace b)

/-- Equivalent norms on the actual auxiliary one-derivative domain. -/
def sourceAuxiliaryDomainEquiv (b : BoundaryCondition) :
    sourceWeightedAuxiliarySubspace (p := p) b 1 ≃L[ℂ] auxiliaryDomain (p := p) b :=
  (WeightedCoeffPair.toMax (Weight.sobolev 1) p).ofSubmodule' (auxiliaryDomain b)

/-- The actual original pencil is conjugate to the existing auxiliary pencil. -/
theorem sourceAuxiliaryPencil_eq_conj (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (z : ℂ) :
    sourceAuxiliaryPencil b hp φ hφ z =
      ((sourceAuxiliaryBaseEquiv b).symm.toContinuousLinearMap.comp
        (auxiliaryPencil b hp (CoeffPair.toMax p φ) hφ z)).comp
        (sourceAuxiliaryDomainEquiv b).toContinuousLinearMap := by
  ext a : 1
  apply Subtype.ext
  change z • (CoeffPair.toMax p).symm (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)) -
      (CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)) =
    (CoeffPair.toMax p).symm (spectralPencil hp (CoeffPair.toMax p φ) z
      (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val))
  rw [spectralPencil_apply, map_sub, map_smul]

/-- Resolvent parameters are defined by actual original-pencil bijectivity. -/
def sourceAuxiliaryResolventSet (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) : Set ℂ :=
  {z | Function.Bijective (sourceAuxiliaryPencil b hp φ hφ z)}

theorem sourceAuxiliaryResolventSet_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) :
    sourceAuxiliaryResolventSet b hp φ hφ = auxiliaryResolventSet b hp (CoeffPair.toMax p φ) hφ := by
  ext z
  change Function.Bijective (sourceAuxiliaryPencil b hp φ hφ z) ↔ _
  rw [sourceAuxiliaryPencil_eq_conj]
  change Function.Bijective ((sourceAuxiliaryBaseEquiv b).symm ∘
    auxiliaryPencil b hp (CoeffPair.toMax p φ) hφ z ∘ sourceAuxiliaryDomainEquiv b) ↔ _
  rw [Function.Bijective.of_comp_iff' (sourceAuxiliaryBaseEquiv b).symm.bijective,
    Function.Bijective.of_comp_iff _ (sourceAuxiliaryDomainEquiv b).bijective]
  rfl

/-- The original auxiliary spectrum is the complement of the actual restricted resolvent set. -/
def sourceAuxiliarySpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) : Set ℂ :=
  (sourceAuxiliaryResolventSet b hp φ hφ)ᶜ

theorem sourceAuxiliarySpectrum_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) :
    sourceAuxiliarySpectrum b hp φ hφ = auxiliarySpectrum b hp (CoeffPair.toMax p φ) hφ := by
  unfold sourceAuxiliarySpectrum auxiliarySpectrum
  rw [sourceAuxiliaryResolventSet_eq]

/-- A sufficient original-norm bound for the restricted operator. -/
theorem norm_sourceAuxiliaryOperator_le (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann)
    (a : sourceWeightedAuxiliarySubspace (p := p) b 1) :
    ‖sourceAuxiliaryOperator b hp φ hφ a‖ ≤ (2 : ℝ)^(1/p.toReal) *
      (Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖a‖ := by
  change ‖(CoeffPair.toMax p).symm (operator hp (CoeffPair.toMax p φ)
    (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val))‖ ≤ _
  calc
    _ ≤ (2 : ℝ)^(1/p.toReal) * ‖operator hp (CoeffPair.toMax p φ)
        (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val)‖ := CoeffPair.norm_toMax_symm_le hp _
    _ ≤ (2 : ℝ)^(1/p.toReal) *
        ((Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖CoeffPair.toMax p φ‖) *
          ‖WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val‖) :=
      mul_le_mul_of_nonneg_left (norm_operator_apply_le hp _ _) (by positivity)
    _ ≤ (2 : ℝ)^(1/p.toReal) *
        ((Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖a.val‖) := by
      gcongr
      · exact add_nonneg Real.pi_pos.le
          (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg _))
      · exact WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp
      · exact CoeffPair.norm_toMax_le φ
      · exact WeightedCoeffPair.norm_toMax_le _ a.val
    _ = _ := by rw [mul_assoc]; rfl

end NLS.ZakharovShabat
