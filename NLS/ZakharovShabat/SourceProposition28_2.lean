import NLS.ZakharovShabat.SourceRealNormalizedActionGapBound
import NLS.ZakharovShabat.SourceNormalizedActionRealPartNeighborhood
import NLS.ZakharovShabat.PhysicalH1NormBound

/-! # Proposition 28.2 on one connected L²-open neighborhood

The same neighborhood works for every M₁ weight. Projection to the real-type
locus contracts the exact weighted norm, so no continuity of a stronger norm
in the L² topology is needed. All statements include collapsed gaps.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A uniform unit error from the real projection leaves room for the printed constant. -/
theorem sourceM1_normalizedAction_le_4608_of_realPart_bound
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2) (n : ℤ)
    (hn : 8*‖a‖^2 ≤ 1+|(n:ℝ)|)
    (hd : ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (normalizedWeightedSource w a)-
      sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
        (sourceRealPart (normalizedWeightedSource w a))‖ ≤ 1) :
    ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
      4608*(1+‖a‖^2) := by
  let b : realTypeSourceSubmodule 2 := ⟨sourceRealPart a,sourceRealPart_realType a⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg (sourceRealPart a)) (norm_sourceRealPart_le (by simp) a) 2
  have hb := sourceM1_real_normalizedAction_le_1536 w hw b n
    (by change 8*‖sourceRealPart a‖^2 ≤ 1+|(n:ℝ)|; linarith)
  change ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
    (normalizedWeightedSource w (sourceRealPart a))‖ ≤ 1536*(1+‖sourceRealPart a‖^2) at hb
  rw [normalizedWeightedSource_sourceRealPart] at hb
  have he := norm_add_le
    (sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (normalizedWeightedSource w a)-
      sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
        (sourceRealPart (normalizedWeightedSource w a)))
    (sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
      (sourceRealPart (normalizedWeightedSource w a)))
  simp only [sub_add_cancel] at he
  linarith [sq_nonneg ‖a‖]

/-- One connected neighborhood in the original L² space, chosen before every weight,
controls the normalized actions and the actual actions with the printed constant. -/
theorem exists_sourceM1_action_gap_neighborhood :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
        normalizedWeightedSource w a ∈ U → ∀ n : ℤ, 8*‖a‖^2 ≤ 1+|(n:ℝ)| →
          (‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
            4608*(1+‖a‖^2)) ∧
          ‖sourceComplexAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
            4608*(1+‖a‖^2)*
              ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w a) n‖^2 := by
  obtain ⟨U,hU,hconn,hreal,hsub,hdata⟩ := exists_sourceNormalizedAction_realPart_neighborhood
  refine ⟨U,hU,hconn,hreal,hsub,?_⟩
  intro w hw a ha n hn
  have h := hdata _ ha n
  have hb := sourceM1_normalizedAction_le_4608_of_realPart_bound w hw a n hn h.1
  refine ⟨hb,?_⟩
  rw [h.2,norm_mul,norm_pow]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
    (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w a) n‖)

/-- The normalized physical coordinates decode to the original H¹ source exactly. -/
@[simp] theorem normalizedWeightedSource_physicalH1Coordinates (a : ScalarDomain 2 × ScalarDomain 2) :
    normalizedWeightedSource (SpectralWeight.piSobolev 1 (by norm_num)) (sourcePhysicalH1Coordinates a) =
      sobolevSourceInclusion a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · change (normalizedWeightedSource _ _).fst = (sobolevSourceInclusion a).fst
    ext n
    simp only [normalizedWeightedSource_fst,sourcePhysicalH1Coordinates_fst,
      sobolevSourceInclusion_fst,SpectralWeight.piSobolev_apply,Real.rpow_one]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))
  · change (normalizedWeightedSource _ _).snd = (sobolevSourceInclusion a).snd
    ext n
    simp only [normalizedWeightedSource_snd,sourcePhysicalH1Coordinates_snd,
      sobolevSourceInclusion_snd,SpectralWeight.piSobolev_apply,Real.rpow_one]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))

/-- Proposition 28.2 for all complex H¹ sources in an open connected neighborhood
of the entire real L² locus, with exact physical norm and threshold. -/
theorem exists_sourceH1_proposition28_2 :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
      U ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion a ∈ U →
        ∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ |(n:ℝ)| →
          ‖sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a)‖ ≤
            4608*(1+‖sourcePhysicalH1Coordinates a‖^2)*
              ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) n‖^2 := by
  obtain ⟨U,hU,hconn,hreal,hsub,hdata⟩ := exists_sourceM1_action_gap_neighborhood
  refine ⟨U,hU,hconn,hreal,hsub,?_⟩
  intro a ha n hn
  have h := hdata (SpectralWeight.piSobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) (sourcePhysicalH1Coordinates a)
    (by simpa only [normalizedWeightedSource_physicalH1Coordinates] using ha) n (by linarith)
  simpa only [normalizedWeightedSource_physicalH1Coordinates] using h.2

end NLS.ZakharovShabat
