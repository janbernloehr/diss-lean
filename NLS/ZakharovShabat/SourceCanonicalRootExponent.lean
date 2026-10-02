import NLS.ZakharovShabat.ExponentSourcePotentials
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-! # Exponent compatibility of the canonical root and its domains

The canonical endpoints retain their signed indices under source
inclusion. Thus the standard roots, their full normalized product,
and the complements of the periodic gap segments agree exactly.
The equality includes spectral zeros and fixes the normalization.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourcePeriodicSegment_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSegment hp hp1 φ n =
      sourcePeriodicSegment hq hq1 (CoeffPair.exponentInclusion hpq φ) n := by
  unfold sourcePeriodicSegment
  rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ).2]

theorem sourceStandardRoot_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 φ n z =
      sourceStandardRoot hq hq1 (CoeffPair.exponentInclusion hpq φ) n z := by
  unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
  rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ).2]

theorem sourceCanonicalRoot_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 φ z =
      sourceCanonicalRoot hq hq1 (CoeffPair.exponentInclusion hpq φ) z := by
  simp only [sourceCanonicalRoot, sourceStandardRootPairedProduct, sourceStandardRootPairedFactor,
    sourceStandardRoot_exponent hp hq hp1 hq1 hpq φ]

theorem sourceCanonicalRootDomain_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) :
    sourceCanonicalRootDomain hp hp1 φ =
      sourceCanonicalRootDomain hq hq1 (CoeffPair.exponentInclusion hpq φ) := by
  simp only [sourceCanonicalRootDomain, sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq φ]

theorem sourceStandardRootOmittedDomain_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (n : ℤ) :
    sourceStandardRootOmittedDomain hp hp1 φ n =
      sourceStandardRootOmittedDomain hq hq1 (CoeffPair.exponentInclusion hpq φ) n := by
  simp only [sourceStandardRootOmittedDomain, sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq φ]

end NLS.ZakharovShabat
