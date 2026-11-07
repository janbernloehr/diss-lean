import NLS.ZakharovShabat.SourceStandardRootPhase
import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness
import NLS.ZakharovShabat.SourceStandardRootOmittedProduct
import NLS.ZakharovShabat.SourceCanonicalRootReflection

/-! Exact canonical-root transport under the actual source phase.
Full spectral data fix every labelled endpoint even for complex sources;
the literal normalized root products therefore retain their signs. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceCanonicalRootDomain_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) :
    sourceCanonicalRootDomain hp hp1 (sourcePhase φ)=sourceCanonicalRootDomain hp hp1 φ := by
  ext z
  simp only [sourceCanonicalRootDomain,sourcePeriodicSegment_sourcePhase]

/-- Literal equality of the full normalized root, including cut points;
equality of squares alone is not used to choose its sign. -/
theorem sourceCanonicalRoot_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourcePhase φ) z=sourceCanonicalRoot hp hp1 φ z := by
  simp only [sourceCanonicalRoot,sourceStandardRootPairedProduct,
    sourceStandardRootPairedFactor,sourceStandardRoot_sourcePhase]

theorem SourcePeriodicReflection.sourcePhase {hp : p≠⊤} {hp1 : 1<p} {φ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 φ) :
    SourcePeriodicReflection hp hp1 (sourcePhase φ) := by
  intro n
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_sourcePhase hp hp1 φ
  simpa only [hl,hr] using h n

end NLS.ZakharovShabat
