import NLS.ZakharovShabat.SourceEtaRemainderLocalGapBound
import NLS.ZakharovShabat.SourceAngularBetaH1BallBound

/-! # Uniform H1 decay of the actual eta remainder

Real interlacing turns the local displacement bound into a gap bound.
Compactness of the physical H1 decoder gives uniform constants on H1
balls, and the weighted gap sequence gives inverse-bracket decay.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- On a compact real source set, the eta remainder is bounded by the actual gap with one constant. -/
theorem etaRemainder_gap_uniform_compact (K : Set (CoeffPair 2)) (hK : IsCompact K)
    (hKreal : K ⊆ realTypeSourceLocus 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ K, ∀ n : ℤ,
      ‖sourceAngularEtaRemainder (by simp) (by norm_num) n s ψ‖ ≤
        C*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖ := by
  classical
  have hl (φ : K) := D.exists_local_uniform_etaRemainder_gap_bound ⟨φ.val,hKreal φ.property⟩
  choose V hV hφV _ C hC hbound using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩)
  refine ⟨∑ φ ∈ S, C φ,Finset.sum_nonneg (fun φ _ => hC φ),?_⟩
  intro ψ hψ n
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hS hψ)
  obtain ⟨hφS,hψV⟩ := mem_iUnion.mp hφ
  have hd := norm_sourceDirichletMidpointDisplacement_le_half_gap ⟨ψ,hKreal hψ⟩ n
  rw [sourceDirichletMidpointDisplacement_apply] at hd
  have hh : ‖sourceAngularEtaRemainder (by simp) (by norm_num) n s ψ‖ ≤
      C φ*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖ :=
    (hbound φ ψ hψV n).trans (mul_le_mul_of_nonneg_left (by linarith) (hC φ))
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun φ _ => hC φ) hφS) (norm_nonneg _))

/-- The eta remainder's gap bound is uniform on physical H1 balls for the original family. -/
theorem etaRemainder_gap_uniform_physical_H1_ball (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, ‖sourceAngularEtaRemainder (by simp) (by norm_num) n s (sobolevSourceInclusion a.val)‖ ≤
        C*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖ := by
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
  obtain ⟨C,hC,hb⟩ := D.etaRemainder_gap_uniform_compact K hK hrealK
  refine ⟨C,hC,?_⟩
  intro a ha
  apply hb
  apply subset_closure
  refine ⟨sourcePhysicalH1Coordinates a.val,⟨?_,sourcePhysicalH1Coordinates_realType a⟩,?_⟩
  · simpa only [mem_closedBall,dist_zero_right] using ha
  · exact normalizedWeightedSource_physicalH1Coordinates a.val

/-- The actual eta remainder decays at inverse-bracket rate uniformly on physical H1 balls. -/
theorem etaRemainder_uniform_physical_H1_decay (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceAngularEtaRemainder (by simp) (by norm_num) n s
        (sobolevSourceInclusion a.val)‖ ≤ K := by
  obtain ⟨C,hC,h⟩ := D.etaRemainder_gap_uniform_physical_H1_ball R
  obtain ⟨M,hM,hgap⟩ := exists_sourceH1WeightedGapSequence_bound_on_physical_ball R
  refine ⟨C*M,mul_nonneg hC hM,?_⟩
  intro a ha n
  have hpoint : ‖sourceH1WeightedGapSequence a.val n‖ ≤ M :=
    (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans (hgap a ha)
  calc
    _ ≤ (1+|(n:ℝ)|)*(C*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖) :=
      mul_le_mul_of_nonneg_left (h a ha n) (by positivity)
    _ = C*((1+|(n:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖) := by ring
    _ ≤ C*‖sourceH1WeightedGapSequence a.val n‖ := mul_le_mul_of_nonneg_left (sourceH1WeightedGapSequence_majorant a.val n) hC
    _ ≤ C*M := mul_le_mul_of_nonneg_left hpoint hC

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
