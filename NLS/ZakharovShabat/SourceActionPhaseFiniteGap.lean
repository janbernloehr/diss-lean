import NLS.ZakharovShabat.SourceActionPhaseGlobalODE
import NLS.ZakharovShabat.SourceActionFiniteGapDifferential

/-! # Actual finite-gap regularity along action-invariant source lifts -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every originally closed gap remains closed at each admissible time;
the full complex action differential there vanishes in every direction. -/
theorem imageFlow_closed_gap_and_action_differential
    (F : SourceActionFrequency hp hp1) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (hτ : (τ,φ) ∈ F.imageDomain D) (n : ℤ)
    (hn : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0) :
    sourcePeriodicGapDisplacement hp hp1 (F.imageFlow D φ τ).val n = 0 ∧
      fderiv ℂ (sourceComplexAction hp hp1 n) (F.imageFlow D φ τ).val = 0 := by
  have hact : sourceComplexAction hp hp1 n (F.imageFlow D φ τ).val = 0 :=
    (F.imageFlow_action D φ τ hτ n).trans
      ((sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n φ.val φ.property).2.2.mpr hn)
  have hg := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n
    (F.imageFlow D φ τ).val (F.imageFlow D φ τ).property).2.2.mp hact
  exact ⟨hg,sourceComplexAction_fderiv_eq_zero_of_closed_gap hp hp1 _ (F.imageFlow D φ τ).property n hg⟩

/-- Actual spectral finite-gap sources remain finite-gap under every
admissible action-invariant image lift, at every finite source exponent. -/
theorem imageFlow_finiteGap (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (τ : ℝ) (hτ : (τ,φ) ∈ F.imageDomain D) : F.imageFlow D φ τ ∈ sourceFiniteGapLocus hp hp1 := by
  apply hf.subset
  intro n hn
  by_contra hnot
  have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply,Set.mem_ofPred_eq,not_not] using hnot
  exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using
    (F.imageFlow_closed_gap_and_action_differential D φ τ hτ n hg).1)

/-- At every finite-gap source, the same finite cutoff supports the action
cotangents at every admissible time, including directions opening a gap. -/
theorem imageFlow_action_differential_support (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (τ : ℝ) (hτ : (τ,φ) ∈ F.imageDomain D) :
    ∀ n ∉ hf.toFinset, fderiv ℂ (sourceComplexAction hp hp1 n) (F.imageFlow D φ τ).val = 0 := by
  intro n hn
  have hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
    rw [sourcePeriodicGapDisplacement_apply]
    by_contra h
    exact hn (hf.mem_toFinset.mpr h)
  exact (F.imageFlow_closed_gap_and_action_differential D φ τ hτ n hg).2

end NLS.ZakharovShabat.SourceActionFrequency
