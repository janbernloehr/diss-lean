import NLS.ZakharovShabat.ClassicalAuxiliarySpace
import NLS.ZakharovShabat.AuxiliaryPhysicalL2
import NLS.ZakharovShabat.ClassicalIntervalOperator

/-!
# The physical auxiliary interval operator

Bounded inclusion and operator maps act on the original auxiliary H¹ domain
and the original physical L² base space. Their phase transport is proved to
realize actual inclusion and the actual differential expression on arbitrary
original representatives.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat.BoundaryCondition

/-- Inclusion of the original auxiliary H¹ domain into physical L². -/
def classicalAuxiliaryInclusion (b : BoundaryCondition) : ClassicalAuxiliaryDomain b →L[ℂ] IntervalPairL2 :=
  intervalAuxiliaryPhase.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((classicalInclusion b).comp (classicalAuxiliaryDomainPhase b).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The original auxiliary operator, with the physical H¹ domain norm. -/
def classicalAuxiliaryOperator (b : BoundaryCondition) (u : IntervalPairL2) :
    ClassicalAuxiliaryDomain b →L[ℂ] IntervalPairL2 :=
  intervalAuxiliaryPhase.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((classicalOperator b (intervalAuxiliaryPotential u)).comp
      (classicalAuxiliaryDomainPhase b).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Domain and base phase rotations intertwine actual inclusion. -/
theorem classicalAuxiliaryInclusion_phase (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    classicalAuxiliaryInclusion b (classicalAuxiliaryDomainPhase b f) = intervalAuxiliaryPhase (classicalInclusion b f) := by
  change intervalAuxiliaryPhase (classicalInclusion b ((classicalAuxiliaryDomainPhase b).symm
    (classicalAuxiliaryDomainPhase b f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- Domain and base phase rotations intertwine the original operators. -/
theorem classicalAuxiliaryOperator_phase (b : BoundaryCondition) (u : IntervalPairL2) (f : ClassicalIntervalDomain b) :
    classicalAuxiliaryOperator b u (classicalAuxiliaryDomainPhase b f) =
      intervalAuxiliaryPhase (classicalOperator b (intervalAuxiliaryPotential u) f) := by
  change intervalAuxiliaryPhase (classicalOperator b (intervalAuxiliaryPotential u)
    ((classicalAuxiliaryDomainPhase b).symm (classicalAuxiliaryDomainPhase b f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem classicalAuxiliaryInclusion_injective (b : BoundaryCondition) :
    Function.Injective (classicalAuxiliaryInclusion b) :=
  intervalAuxiliaryPhase.injective.comp ((classicalInclusion_injective b).comp
    (classicalAuxiliaryDomainPhase b).symm.injective)

theorem classicalAuxiliaryInclusion_denseRange (b : BoundaryCondition) :
    DenseRange (classicalAuxiliaryInclusion b) :=
  intervalAuxiliaryPhase.surjective.denseRange.comp
    ((classicalInclusion_denseRange b).comp (classicalAuxiliaryDomainPhase b).symm.surjective.denseRange
      (classicalInclusion b).continuous) intervalAuxiliaryPhase.continuous

/-- Original auxiliary domain representatives are square integrable. -/
theorem memLp_classicalAuxiliaryDomainRepresentative (b : BoundaryCondition) (f : ClassicalAuxiliaryDomain b) :
    MemLp (classicalAuxiliaryDomainRepresentative b f) 2 (volume.restrict (Ioc 0 1)) := by
  have h := memLp_classicalDomainRepresentative b ((classicalAuxiliaryDomainPhase b).symm f)
  exact memLp_prod_iff.mpr ⟨h.fst, h.snd.const_smul Complex.I⟩

/-- Physical inclusion sends the actual auxiliary function to precisely its L² class. -/
theorem classicalAuxiliaryInclusion_representative (b : BoundaryCondition) (f : ClassicalAuxiliaryDomain b) :
    classicalAuxiliaryInclusion b f = intervalL2OfFunction (classicalAuxiliaryDomainRepresentative b f)
      (memLp_classicalAuxiliaryDomainRepresentative b f) := by
  change intervalAuxiliaryPhase (classicalInclusion b ((classicalAuxiliaryDomainPhase b).symm f)) = _
  rw [classicalInclusion_representative]
  exact intervalAuxiliaryPhase_ofFunction _ _ _

/-- Inclusion retains any original representative on its interval. -/
theorem classicalAuxiliaryInclusion_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (hL : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    classicalAuxiliaryInclusion b (classicalAuxiliaryDomainOfFunction b f hf) = intervalL2OfFunction f hL := by
  rw [classicalAuxiliaryInclusion_representative]
  apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact classicalAuxiliaryDomainRepresentative_apply b (classicalAuxiliaryDomainOfFunction b f hf)
    ⟨x, Ioc_subset_Icc_self hx⟩

/-- The transported auxiliary operator realizes the actual physical differential expression. -/
theorem classicalAuxiliaryOperator_realization (b : BoundaryCondition) (u : IntervalPairL2)
    (f : ClassicalAuxiliaryDomain b) :
    intervalL2Representative (classicalAuxiliaryOperator b u f) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalOperator (intervalL2Representative u) (classicalAuxiliaryDomainRepresentative b f) := by
  let g := (classicalAuxiliaryDomainPhase b).symm f
  have ho := classicalOperator_realization b (intervalAuxiliaryPotential u) g
  have hp := intervalL2Representative_auxiliaryPotential u
  have hg := intervalL2Representative_auxiliaryPhase (classicalOperator b (intervalAuxiliaryPotential u) g)
  filter_upwards [ho, hp, hg] with x ho hp hg
  change intervalL2Representative (intervalAuxiliaryPhase (classicalOperator b (intervalAuxiliaryPotential u) g)) x =
    physicalOperator (intervalL2Representative u) (physicalAuxiliaryPhase (classicalDomainRepresentative b g)) x
  rw [congrFun (physicalOperator_auxiliaryPhase (intervalL2Representative u) (classicalDomainRepresentative b g)) x]
  rw [hg]
  change auxiliaryPhase ℂ (intervalL2Representative (classicalOperator b (intervalAuxiliaryPotential u) g) x) = _
  rw [ho]
  simp only [physicalAuxiliaryPhase_apply, physicalOperator, hp]
  rfl

/-- The physical operator equation holds for arbitrary original input representatives. -/
theorem classicalAuxiliaryOperator_realization_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) :
    intervalL2Representative (classicalAuxiliaryOperator b (intervalL2OfFunction φ hφ)
      (classicalAuxiliaryDomainOfFunction b f hf)) =ᵐ[volume.restrict (Ioc 0 1)] physicalOperator φ f := by
  apply (classicalAuxiliaryOperator_realization b _ _).trans
  apply physicalOperator_congr_on_interval (intervalL2Representative_ofFunction φ hφ)
  intro x hx
  exact classicalAuxiliaryDomainRepresentative_apply b (classicalAuxiliaryDomainOfFunction b f hf) ⟨x, hx⟩

/-- Every actual auxiliary operator output is square integrable. -/
theorem memLp_classicalAuxiliaryOperator_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) :
    MemLp (physicalOperator φ f) 2 (volume.restrict (Ioc 0 1)) :=
  (memLp_congr_ae (classicalAuxiliaryOperator_realization_ofFunction b φ f hφ hf)).mp (memLp_intervalL2Representative _)

/-- The auxiliary operator returns the actual L² class of the original differential expression. -/
theorem classicalAuxiliaryOperator_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalAuxiliaryDomain b f) :
    classicalAuxiliaryOperator b (intervalL2OfFunction φ hφ) (classicalAuxiliaryDomainOfFunction b f hf) =
      intervalL2OfFunction (physicalOperator φ f) (memLp_classicalAuxiliaryOperator_ofFunction b φ f hφ hf) := by
  apply intervalL2Representative_injective
  exact (classicalAuxiliaryOperator_realization_ofFunction b φ f hφ hf).trans
    (intervalL2Representative_ofFunction _ _).symm

end NLS.ZakharovShabat.BoundaryCondition
