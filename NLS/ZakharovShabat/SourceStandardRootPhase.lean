import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.SourceStandardRootOmittedProduct
import NLS.ZakharovShabat.SourceStandardRootGapSideSource

/-! The actual signed endpoint labels, standard roots and literal
omitted products are unchanged by the fixed source phase. There is no
relabeling, square-root sign choice or unspecified product scalar. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem canonicalPeriodicMidpoint_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n := by
  unfold canonicalPeriodicMidpoint
  rw [(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).1,(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).2]

theorem canonicalPeriodicGap_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n := by
  unfold canonicalPeriodicGap
  rw [(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).1,(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).2]

theorem sourcePeriodicSegment_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSegment hp hp1 (sourcePhase φ) n=sourcePeriodicSegment hp hp1 φ n := by
  unfold sourcePeriodicSegment
  rw [(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).1,(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).2]

theorem sourceStandardRoot_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 (sourcePhase φ) n z=sourceStandardRoot hp hp1 φ n z := by
  unfold sourceStandardRoot
  rw [canonicalPeriodicMidpoint_sourcePhase,canonicalPeriodicGap_sourcePhase]

theorem sourceStandardRootOmittedProduct_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n (sourcePhase φ) z=
      sourceStandardRootOmittedProduct hp hp1 n φ z := by
  simp only [sourceStandardRootOmittedProduct,sourceStandardRootOmittedPairedFactor,
    omittedSymmetricPairFactor,sourceStandardRoot_sourcePhase]

theorem sourceStandardRootOmittedDomain_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceStandardRootOmittedDomain hp hp1 (sourcePhase φ) n=sourceStandardRootOmittedDomain hp hp1 φ n := by
  simp only [sourceStandardRootOmittedDomain,sourcePeriodicSegment_sourcePhase]

end NLS.ZakharovShabat
