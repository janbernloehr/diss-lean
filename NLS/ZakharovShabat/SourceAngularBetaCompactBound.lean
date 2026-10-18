import NLS.ZakharovShabat.SourceBirkhoffH1PhaseDecay
import NLS.ZakharovShabat.SourceSection28Asymptotics

/-! # Uniform off-diagonal beta bounds on physical H1 balls

A finite subcover supplies one beta constant on each compact subset of
the angular domain. The existing compact normalized weighted decoder
then gives one constant on each physical H1 ball for the same original
Birkhoff family. All selected and integration indices are controlled.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData
variable {W₀ B : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Compact subsets have one off-diagonal beta constant for all selected and integration indices. -/
theorem beta_uniform_compact
    (D : SourceAngularEtaLocalCommonDomainData (by simp) (by norm_num) W₀ B s)
    (K : Set (CoeffPair 2)) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ K, ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta (by simp) (by norm_num) n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ m -
            sourceStandardRootMidpoint (by simp) (by norm_num) ψ m‖) / |((n-m:ℤ):ℝ)| := by
  classical
  have hl (φ : K) := D.beta_bound φ.val (hKB φ.property)
  choose V hV hφV _ C hC hbeta using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩)
  refine ⟨∑ φ ∈ S, C φ,Finset.sum_nonneg (fun φ _ => (hC φ).le),?_⟩
  intro ψ hψ n m hmn
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hS hψ)
  obtain ⟨hφS,hψV⟩ := mem_iUnion.mp hφ
  apply (hbeta φ ψ hψV n m hmn).trans
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun φ _ => (hC φ).le) hφS) (by positivity)

end NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Physical H1 balls have a uniform off-diagonal beta constant. -/
theorem beta_uniform_physical_H1_ball (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n m : ℤ, m ≠ n →
        ‖sourceAngularBeta (by simp) (by norm_num) n m s (sobolevSourceInclusion a.val)‖ ≤ C *
          (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) m‖ +
            ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (sobolevSourceInclusion a.val) m -
              sourceStandardRootMidpoint (by simp) (by norm_num) (sobolevSourceInclusion a.val) m‖) / |((n-m:ℤ):ℝ)| := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let X := closedBall (0 : CoeffPair 2) R ∩ realTypeSourceLocus 2
  let K := closure (normalizedWeightedSource w '' X)
  have hbounded : Bornology.IsBounded X := isBounded_closedBall.subset inter_subset_left
  have hK : IsCompact K :=
    IsCompactOperator.isCompact_closure_image_of_bounded
      (f := (normalizedWeightedSourceCLM (p := 2) w).toLinearMap)
      (isCompactOperator_normalizedWeightedSource w (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl)) hbounded
  have hrealK : K ⊆ realTypeSourceLocus 2 :=
    closure_minimal (by rintro _ ⟨a,ha,rfl⟩; exact normalizedWeightedSource_realType w a ha.2)
      isClosed_realTypeSourceLocus
  obtain ⟨C,hC,hb⟩ := D.angular.beta_uniform_compact K hK
    (hrealK.trans (D.real_subset.trans D.source_subset))
  refine ⟨C,hC,?_⟩
  intro a ha
  apply hb
  apply subset_closure
  refine ⟨sourcePhysicalH1Coordinates a.val,⟨?_,sourcePhysicalH1Coordinates_realType a⟩,?_⟩
  · simpa only [mem_closedBall,dist_zero_right] using ha
  · exact normalizedWeightedSource_physicalH1Coordinates a.val

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
