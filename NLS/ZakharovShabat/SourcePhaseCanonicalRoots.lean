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

theorem canonicalPeriodicEndpoints_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourcePhase φ)) (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) :=
  canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 _ _
    (periodOnePotential_mem _) (periodOnePotential_mem _)
    (periodicSpectrum_periodOne_sourcePhase hp φ)
    (periodicAlgebraicMultiplicity_periodOne_sourcePhase hp φ)

theorem sourcePeriodicSegment_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSegment hp hp1 (sourcePhase φ) n=sourcePeriodicSegment hp hp1 φ n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_sourcePhase hp hp1 φ
  unfold sourcePeriodicSegment
  rw [hl,hr]

theorem sourceCanonicalRootDomain_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) :
    sourceCanonicalRootDomain hp hp1 (sourcePhase φ)=sourceCanonicalRootDomain hp hp1 φ := by
  ext z
  simp only [sourceCanonicalRootDomain,sourcePeriodicSegment_sourcePhase]

theorem sourceStandardRoot_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 (sourcePhase φ) n z=sourceStandardRoot hp hp1 φ n z := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_sourcePhase hp hp1 φ
  unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
  rw [hl,hr]

/-- Literal equality of the full normalized root, including cut points;
equality of squares alone is not used to choose its sign. -/
theorem sourceCanonicalRoot_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourcePhase φ) z=sourceCanonicalRoot hp hp1 φ z := by
  simp only [sourceCanonicalRoot,sourceStandardRootPairedProduct,
    sourceStandardRootPairedFactor,sourceStandardRoot_sourcePhase]

/-- The complete omitted product has the same normalization, at every
signed omitted index and every frequency, including its selected cut. -/
theorem sourceStandardRootOmittedProduct_sourcePhase (hp : p≠⊤) (hp1 : 1<p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n (sourcePhase φ) z=
      sourceStandardRootOmittedProduct hp hp1 n φ z := by
  simp only [sourceStandardRootOmittedProduct,sourceStandardRootOmittedPairedFactor,
    sourceStandardRoot_sourcePhase]

theorem SourcePeriodicReflection.sourcePhase {hp : p≠⊤} {hp1 : 1<p} {φ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 φ) :
    SourcePeriodicReflection hp hp1 (sourcePhase φ) := by
  intro n
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_sourcePhase hp hp1 φ
  simpa only [hl,hr] using h n

end NLS.ZakharovShabat
