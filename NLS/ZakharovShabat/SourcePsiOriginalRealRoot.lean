import NLS.ZakharovShabat.SourcePsiOriginalRealEquation
import NLS.ZakharovShabat.SourcePsiOmegaDomain

/-!
# The original real psi root map

The canonical gap solution gives an actual real deleted lp vector.
Complex inclusion recovers the existing root map exactly. The map is
real analytic, solves the original equation at every real-type source,
and has the exact gap placement and free-source normalization.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical solution with the real deleted lp space as codomain. -/
def sourcePsiOriginalRootReal (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) : RealDeletedCoeff p n :=
  RealDeletedCoeff.reCLM n (sourcePsiGapRoot hp hp1 n φ)

/-- Complex inclusion recovers the canonical gap-root solution. -/
theorem sourcePsiOriginalRootReal_complex (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) :
    RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ) = sourcePsiGapRoot hp hp1 n φ :=
  RealDeletedCoeff.complex_re n _ (sourcePsiGapRoot_mem_realDeletedCoeffSubmodule hp hp1 n φ)

/-- Real analyticity on the entire real source Banach space. -/
theorem analyticOnNhd_sourcePsiOriginalRootReal (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℝ (sourcePsiOriginalRootReal hp hp1 n) univ := by
  intro φ _
  exact ((RealDeletedCoeff.reCLM n).analyticAt _).comp (analyticAt_sourcePsiGapRoot_real hp hp1 n φ)

/-- Each retained root lies in its actual periodic gap. -/
theorem sourcePsiOriginalRootReal_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceSubmodule p) :
    displacedRoots (RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ):Coeff p) m ∈
      sourcePeriodicSegment hp hp1 φ m := by
  rw [sourcePsiOriginalRootReal_complex]
  exact sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ

/-- The same root map solves the actual original real equation everywhere. -/
theorem SourceLemma12_4Data.originalRootReal_solves
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    sourcePsiOriginalRealEquation hp hp1 n (sourcePsiOriginalRootReal hp hp1 n φ) φ = 0 := by
  obtain ⟨U,_,_,hRU,s,hS⟩ := H.previous.psiFunctions hW hR
  have he := hS.originalEquation_zero hW φ (hRU φ.property) n
  rw [hS.real_agreement n φ] at he
  simp only [sourcePsiOriginalRealEquation, sourcePsiOriginalRootReal_complex, he, map_zero]

/-- The free source has zero displacement. -/
@[simp] theorem sourcePsiOriginalRootReal_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourcePsiOriginalRootReal hp hp1 n (0:realTypeSourceSubmodule p) = 0 := by
  change RealDeletedCoeff.reCLM n (sourcePsiGapRoot hp hp1 n
    (⟨0,by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p)) = 0
  rw [sourcePsiGapRoot_zero, map_zero]

end NLS.ZakharovShabat
