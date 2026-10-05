import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport
import NLS.ZakharovShabat.SourceBirkhoffProposition17_2

/-! # A real source with all gaps closed is zero

The exact zero criterion for the Birkhoff coordinates and global
injectivity prove the assertion at every finite exponent above one.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Closing all actual periodic gaps characterizes the zero real source. -/
theorem real_source_all_gaps_closed_iff_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    (∀ n, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0) ↔
      φ = 0 := by
  have hzero (n : ℤ) : sourcePeriodicGapDisplacement hp hp1 (0 : CoeffPair p) n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply,map_zero] using canonicalPeriodicGap_zero hp hp1 n
  constructor
  · intro hφ
    obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
    have hφc (n : ℤ) := (D.real_coordinates_zero_iff_gap_zero φ n).mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hφ n)
    have h0c (n : ℤ) := (D.real_coordinates_zero_iff_gap_zero 0 n).mpr (hzero n)
    apply D.proposition17_2
    apply Prod.ext
    · ext n
      exact (hφc n).1.trans (h0c n).1.symm
    · ext n
      exact (hφc n).2.trans (h0c n).2.symm
  · rintro rfl n
    simpa only [sourcePeriodicGapDisplacement_apply] using! hzero n

end NLS.ZakharovShabat
