import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.SourceAngularBetaRegularAnalytic

/-! The ACTUAL auxiliary boundary roots lie in the literal ORIGINAL
periodic gap segments at real-type sources. The phase rotation is
retained; no equality with the unrotated ordinary roots is asserted. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ) :
    canonicalAuxiliaryPeriodOneRoots hp hp1 b φ m ∈ sourcePeriodicSegment hp hp1 φ m := by
  have h := canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 b
    (sourcePhase φ) (isRealType_sourcePhase φ hreal) m
  change canonicalPeriodOneBoundaryRoots hp hp1 b (sourcePhase φ) m ∈
    segment ℝ (canonicalPeriodicLeft hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) m)
      (canonicalPeriodicRight hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) m) at h
  rw [(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).1,(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).2] at h
  rw [canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]
  exact h

end NLS.ZakharovShabat
