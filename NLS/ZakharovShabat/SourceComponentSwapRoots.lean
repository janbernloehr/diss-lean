import NLS.ZakharovShabat.SourceComponentSwapEndpoints
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.SourceStandardRootGapSideSource

/-! # Actual standard roots and the canonical root under component swap

Endpoint label reflection fixes the midpoints, oriented gaps and principal
square-root radicands. Nonzero factors exchange in pairs; the central factor
supplies the minus sign of the full canonical root. These equalities retain
all zero gaps and all complex sources, without dividing by a gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The oriented periodic gap keeps its sign while its index reverses. -/
theorem sourcePeriodicGap_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ n
  unfold canonicalPeriodicGap
  rw [hl,hr]
  ring

/-- The actual source gap sequence is reflected without rescaling. -/
theorem sourcePeriodicGapDisplacement_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    sourcePeriodicGapDisplacement hp hp1 (sourceComponentSwap φ) =
      Coeff.reflection (sourcePeriodicGapDisplacement hp hp1 φ) := by
  ext n
  simp only [sourcePeriodicGapDisplacement_apply,Coeff.reflection_apply]
  exact sourcePeriodicGap_componentSwap hp hp1 φ n

/-- The canonical pair midpoint reflects both its spectral value and index. -/
theorem sourceStandardRootMidpoint_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceStandardRootMidpoint hp hp1 (sourceComponentSwap φ) n =
      -sourceStandardRootMidpoint hp hp1 φ (-n) := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ n
  dsimp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint]
  rw [hl,hr]
  ring

/-- The actual half-gap has no artificial sign under index reflection. -/
theorem sourceStandardRootHalfGap_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceStandardRootHalfGap hp hp1 (sourceComponentSwap φ) n =
      sourceStandardRootHalfGap hp hp1 φ (-n) := by
  exact congrArg (·/2) (sourcePeriodicGap_componentSwap hp hp1 φ n)

/-- The principal normalized root transforms without any branch choice. -/
theorem normalizedStandardRoot_neg_midpoint (t g z : ℂ) :
    normalizedStandardRoot (-t) g (-z) = -normalizedStandardRoot t g z := by
  unfold normalizedStandardRoot
  have he : -t- -z = -(t-z) := by ring
  rw [he,neg_sq,neg_mul]

/-- Each actual standard root has the exact reflected spectral sign,
including its total value at the midpoint and every collapsed gap. -/
theorem sourceStandardRoot_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 (sourceComponentSwap φ) n (-z) = -sourceStandardRoot hp hp1 φ (-n) z := by
  change normalizedStandardRoot (sourceStandardRootMidpoint hp hp1 (sourceComponentSwap φ) n)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n)^2) (-z) = _
  rw [sourceStandardRootMidpoint_componentSwap,sourcePeriodicGap_componentSwap,normalizedStandardRoot_neg_midpoint]
  rfl

/-- Paired nonzero standard-root factors exchange without changing their value. -/
theorem sourceStandardRootPairedFactor_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) (j : ℕ) :
    sourceStandardRootPairedFactor hp hp1 (sourceComponentSwap φ) (-z) j =
      sourceStandardRootPairedFactor hp hp1 φ z j := by
  dsimp only [sourceStandardRootPairedFactor]
  rw [sourceStandardRoot_componentSwap,sourceStandardRoot_componentSwap,neg_neg]
  ring

/-- The complete paired infinite product retains its actual value. -/
theorem sourceStandardRootPairedProduct_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceStandardRootPairedProduct hp hp1 (sourceComponentSwap φ) (-z) =
      sourceStandardRootPairedProduct hp hp1 φ z := by
  unfold sourceStandardRootPairedProduct
  exact tprod_congr (sourceStandardRootPairedFactor_componentSwap hp hp1 φ z)

/-- The central standard-root factor supplies the exact minus sign of the
full canonical root under component swap and spectral reflection. -/
theorem sourceCanonicalRoot_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourceComponentSwap φ) (-z) = -sourceCanonicalRoot hp hp1 φ z := by
  unfold sourceCanonicalRoot
  rw [sourceStandardRoot_componentSwap,neg_zero,sourceStandardRootPairedProduct_componentSwap]
  ring

/-- On the actual mKdV diagonal, every oriented periodic gap is even in its
signed index, with no restriction to finite-gap sources. -/
theorem sourcePeriodicGapDisplacement_even_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : φ.fst = φ.snd) (n : ℤ) :
    sourcePeriodicGapDisplacement hp hp1 φ (-n) = sourcePeriodicGapDisplacement hp hp1 φ n := by
  have he := congrArg (fun a : Coeff p => a n) (sourcePeriodicGapDisplacement_componentSwap hp hp1 φ)
  rw [(sourceComponentSwap_eq_self_iff φ).mpr hφ] at he
  exact he.symm

/-- The actual mKdV canonical root is odd in the spectral parameter. -/
theorem sourceCanonicalRoot_odd_of_diagonal (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : φ.fst = φ.snd) (z : ℂ) :
    sourceCanonicalRoot hp hp1 φ (-z) = -sourceCanonicalRoot hp hp1 φ z := by
  have he := sourceCanonicalRoot_componentSwap hp hp1 φ z
  rw [(sourceComponentSwap_eq_self_iff φ).mpr hφ] at he
  exact he

end NLS.ZakharovShabat
