import NLS.ZakharovShabat.NormalizedWeightedSourceCompact
import NLS.ZakharovShabat.SourceSection11OriginalEstimates
import NLS.ZakharovShabat.SourceProposition28_2

/-! # The ℓ² asymptotic estimate (5.14)

The original filled normalized actions have a locally uniform ℓ² deviation
from one. Compact decoding upgrades this to a uniform bound on each real
M₁ weighted ball, in particular every bounded physical H¹ set.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Formula (5.14), locally uniform on the entire original complex domain. -/
theorem SourceSection11OriginalEstimates.section28_locally_uniform
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (φ : CoeffPair 2) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∃ b : Coeff 2,
        (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n ψ-1) ∧ ‖b‖ ≤ C := by
  obtain ⟨V,hV,hφV,hVW,Gχ,GA,Bχ,BA,he,⟨K,hK,hGA⟩,hBA⟩ := H.locally_uniform φ hφ
  obtain ⟨L,hL,hBA2⟩ := hBA 2 (by norm_num) (by simp)
  let : Fact (1 ≤ (2:ℝ≥0∞)/2) := ⟨by norm_num [ENNReal.div_self]⟩
  have hhalf : (2:ℝ≥0∞)/2 ≤ 2 := by norm_num [ENNReal.div_self]
  refine ⟨V,hV,hφV,hVW,K+L,by positivity,?_⟩
  intro ψ hψ
  refine ⟨Coeff.exponentInclusion hhalf (GA ψ)+CoeffOnePlus.toCoeff 2 (by norm_num) (by simp) (BA ψ),?_,?_⟩
  · intro n
    simpa only [lp.coeFn_add,Pi.add_apply,Coeff.exponentInclusion_apply,CoeffOnePlus.toCoeff_apply] using
      (he ψ hψ n).2.symm
  · exact (norm_add_le _ _).trans (add_le_add
      ((Coeff.norm_exponentInclusion_le hhalf _).trans (hGA ψ hψ).2) (hBA2 ψ hψ).2)

/-- One ℓ² norm bound over every compact subset of the original domain. -/
theorem SourceSection11OriginalEstimates.section28_uniform_compact
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (K : Set (CoeffPair 2)) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ K, ∃ b : Coeff 2,
      (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n ψ-1) ∧ ‖b‖ ≤ C := by
  classical
  have hl (φ : K) := H.section28_locally_uniform φ.val (hKW φ.property)
  choose V hV hφV _ C hC hb using hl
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV (fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩)
  refine ⟨∑ φ ∈ s, C φ,Finset.sum_nonneg (fun φ _ => hC φ),?_⟩
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hs hψ)
  obtain ⟨hφs,hψV⟩ := mem_iUnion.mp hφ
  obtain ⟨b,hbval,hbn⟩ := hb φ ψ hψV
  exact ⟨b,hbval,hbn.trans (Finset.single_le_sum (fun φ _ => hC φ) hφs)⟩

/-- The local estimate is uniform on each real M₁ weighted ball. -/
theorem SourceSection11OriginalEstimates.section28_uniform_weighted_ball
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (hrW : realTypeSourceLocus 2 ⊆ W)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSourceSubmodule 2, ‖a.val‖ ≤ R → ∃ b : Coeff 2,
      (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n
        (normalizedWeightedSource w a.val)-1) ∧ ‖b‖ ≤ C := by
  let X := Metric.closedBall (0 : CoeffPair 2) R ∩ realTypeSourceLocus 2
  let K := closure (normalizedWeightedSource w '' X)
  have hbounded : Bornology.IsBounded X := Metric.isBounded_closedBall.subset inter_subset_left
  have hK : IsCompact K := by
    have h := IsCompactOperator.isCompact_closure_image_of_bounded
      (f := (normalizedWeightedSourceCLM (p := 2) w).toLinearMap)
      (isCompactOperator_normalizedWeightedSource w hw) hbounded
    exact h
  have hrealK : K ⊆ realTypeSourceLocus 2 :=
    closure_minimal (by rintro _ ⟨a,ha,rfl⟩; exact normalizedWeightedSource_realType w a ha.2)
      isClosed_realTypeSourceLocus
  obtain ⟨C,hC,hb⟩ := H.section28_uniform_compact K hK (hrealK.trans hrW)
  refine ⟨C,hC,?_⟩
  intro a ha
  apply hb _ (subset_closure ?_)
  exact ⟨a.val,⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using ha,a.property⟩,rfl⟩



/-- Physical H¹ coordinates preserve the real source condition. -/
theorem sourcePhysicalH1Coordinates_realType (a : realTypeSobolevSourceLocus) :
    IsRealType (CoeffPair.toMax 2 (sourcePhysicalH1Coordinates a.val)) := by
  intro n
  change (sourcePhysicalH1Coordinates a.val).snd n = conj ((sourcePhysicalH1Coordinates a.val).fst (-n))
  rw [sourcePhysicalH1Coordinates_snd,sourcePhysicalH1Coordinates_fst]
  have hr := a.property n
  change (sobolevSourceInclusion a.val).snd n = conj ((sobolevSourceInclusion a.val).fst (-n)) at hr
  simp only [sobolevSourceInclusion_snd,sobolevSourceInclusion_fst] at hr
  rw [hr]
  simp only [mul_neg,Int.cast_neg,neg_mul,abs_neg,map_mul,Complex.conj_ofReal]

/-- The bounded-H¹ assertion following (5.14), in the exact physical pair norm. -/
theorem SourceSection11OriginalEstimates.section28_uniform_physical_H1_ball
    {W : Set (CoeffPair 2)} (H : SourceSection11OriginalEstimates (by simp) (by norm_num) W)
    (hrW : realTypeSourceLocus 2 ⊆ W) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∃ b : Coeff 2, (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n
        (sobolevSourceInclusion a.val)-1) ∧ ‖b‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := H.section28_uniform_weighted_ball hrW (SpectralWeight.piSobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) R
  refine ⟨C,hC,?_⟩
  intro a ha
  simpa only [normalizedWeightedSource_physicalH1Coordinates] using
    hb ⟨sourcePhysicalH1Coordinates a.val,sourcePhysicalH1Coordinates_realType a⟩ ha

end NLS.ZakharovShabat
