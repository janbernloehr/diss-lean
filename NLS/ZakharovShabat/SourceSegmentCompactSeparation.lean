import NLS.ZakharovShabat.SourceSegmentIndexSeparation
import NLS.ZakharovShabat.SourceSection28Asymptotics

/-! # Uniform gap separation on compact source sets and physical H1 balls

A finite subcover gives one index-scale gap separation constant on each
compact set of real sources. Compact normalized weighted decoding transfers
this to every physical H1 ball. All points of the actual gaps are included.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact set of real sources has one index-scale separation constant for all gap points. -/
theorem exists_source_segment_index_separation_on_compact
    (hp : p ≠ ⊤) (hp1 : 1 < p) (K : Set (CoeffPair p))
    (hK : IsCompact K) (hKreal : K ⊆ realTypeSourceLocus p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ψ ∈ K, ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourcePeriodicSegment hp hp1 ψ i, ∀ w ∈ sourcePeriodicSegment hp hp1 ψ j,
        |((i-j : ℤ) : ℝ)| ≤ C * ‖w-z‖ := by
  classical
  have hl (φ : K) := exists_local_source_segment_index_separation hp hp1 φ.val (hKreal φ.property)
  choose V hV _ hφV C hC hsep using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩)
  have hsum : 0 ≤ ∑ φ ∈ S, C φ := Finset.sum_nonneg (fun φ _ => (by linarith [hC φ]))
  refine ⟨1 + ∑ φ ∈ S, C φ,by linarith,?_⟩
  intro ψ hψ i j hij z hz w hw
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hS hψ)
  obtain ⟨hφS,hψV⟩ := mem_iUnion.mp hφ
  apply (hsep φ ψ hψV i j hij z hz w hw).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hc : C φ ≤ ∑ φ ∈ S, C φ := Finset.single_le_sum (fun φ _ => (by linarith [hC φ])) hφS
  linarith

/-- Each physical H1 ball has one separation constant for all points of every distinct gap pair. -/
theorem exists_source_segment_index_separation_on_physical_H1_ball (R : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ i j : ℤ, i ≠ j →
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (sobolevSourceInclusion a.val) i,
        ∀ w ∈ sourcePeriodicSegment (by simp) (by norm_num) (sobolevSourceInclusion a.val) j,
          |((i-j : ℤ) : ℝ)| ≤ C * ‖w-z‖ := by
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
  obtain ⟨C,hC,hb⟩ := exists_source_segment_index_separation_on_compact (by simp) (by norm_num) K hK hrealK
  refine ⟨C,hC,?_⟩
  intro a ha
  apply hb
  apply subset_closure
  refine ⟨sourcePhysicalH1Coordinates a.val,⟨?_,sourcePhysicalH1Coordinates_realType a⟩,?_⟩
  · simpa only [mem_closedBall,dist_zero_right] using ha
  · exact normalizedWeightedSource_physicalH1Coordinates a.val

end NLS.ZakharovShabat
