import NLS.ZakharovShabat.SourceFiniteGapBoundaryRatio
import NLS.ZakharovShabat.FiniteRootRatioFirstCoefficient

/-! # The first boundary-quotient coefficient for finite-gap sources

The actual Dirichlet/Neumann quotient, expressed in the inverse spectral
parameter, has a rational germ at zero. Its first coefficient is bounded
by the sum of the finitely many open gap lengths. Identifying that
coefficient with a physical potential value requires a separate proof.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite boundary-root trace is bounded by the corresponding gap sum. -/
theorem norm_sum_boundaryRoot_difference_le_gap_sum
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (s : Finset ℤ) :
    ‖∑ n ∈ s, (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n -
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)‖ ≤
      ∑ n ∈ s, ‖canonicalPeriodicGap hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ) n‖ := by
  calc
    _ ≤ ∑ n ∈ s, ‖canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n -
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun n _ =>
      norm_boundaryRoots_sub_le_periodicGap hp hp1 φ hφ .neumann .dirichlet n

/-- A finite-gap boundary quotient has a normalized rational germ whose first
coefficient is the finite root trace and is bounded by the total gap length. -/
theorem exists_sourceFiniteGap_boundaryCharacteristic_germ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ (s : Finset ℤ) (g : ℂ → ℂ),
      (∀ n : ℤ, n ∈ s ↔ canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) ∧
      g 0 = 1 ∧
      HasDerivAt g (∑ n ∈ s, (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ.val n -
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)) 0 ∧
      ‖deriv g 0‖ ≤ ∑ n ∈ s, ‖canonicalPeriodicGap hp hp1
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖ ∧
      ∀ z : ℂ, z.im ≠ 0 → g (z⁻¹) =
        periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val z /
          periodOneBoundaryCharacteristic hp hp1 .neumann φ.val z := by
  obtain ⟨s,hs,hr⟩ := exists_sourceFiniteGap_boundaryCharacteristic_ratio hp hp1 φ hf
  let ξ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val
  let η := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ.val
  refine ⟨s,finiteRootRatioAtInfinity s ξ η,hs,
    finiteRootRatioAtInfinity_zero s ξ η,
    hasDerivAt_finiteRootRatioAtInfinity_zero s ξ η,?_,?_⟩
  · rw [(hasDerivAt_finiteRootRatioAtInfinity_zero s ξ η).deriv]
    exact norm_sum_boundaryRoot_difference_le_gap_sum hp hp1 φ.val φ.property s
  · intro z hz
    have hz0 : z ≠ 0 := fun h => hz (by simp [h])
    rw [finiteRootRatioAtInfinity_inv s ξ η z hz0]
    exact (hr z hz).symm

end NLS.ZakharovShabat
