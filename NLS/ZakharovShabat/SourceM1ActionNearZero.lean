import NLS.ZakharovShabat.SourceM1ActionContinuity
import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceContinuity
import NLS.ZakharovShabat.SourceNormalizedActionFree

/-! # The weighted complex action estimate at the zero potential -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single neighborhood of zero controls all normalized action factors. -/
theorem exists_zero_sourceAction_gap_bound :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ (0:CoeffPair 2) ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, ‖sourceComplexAction (by simp) (by norm_num) n ψ‖ ≤
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖^2 := by
  have hzero := (0 : realTypeSourceSubmodule 2).property
  obtain ⟨V,hV,h0V,F,hval,hcont⟩ := exists_local_sourceNormalizedActionDeviation_continuousMap
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) (by norm_num : (1:ℝ≥0∞) < 2)
    (by simp) (by norm_num) 0 hzero
  obtain ⟨G,hG,h0G,_,hfactor⟩ := exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (by simp) (by norm_num) 0 hzero
  have hF0 : F 0 = 0 := by
    ext n
    rw [hval 0 h0V n]
    simp [sourceNormalizedActionDeviation,sourceNormalizedActionComplexExtension_zero_source]
  have hsmall : ∀ᶠ ψ : CoeffPair 2 in 𝓝 0, ‖F ψ‖ < 1 :=
    ((hcont 0 h0V).continuousAt (hV.mem_nhds h0V)).norm.eventually
      (gt_mem_nhds (by simp only [hF0,norm_zero]; norm_num))
  obtain ⟨O,hOsub,hO,h0O⟩ := _root_.mem_nhds_iff.mp hsmall
  let U := (V ∩ G) ∩ O
  refine ⟨U,(hV.inter hG).inter hO,⟨⟨h0V,h0G⟩,h0O⟩,?_⟩
  intro ψ hψ n
  have hb (k : ℤ) : ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) k ψ‖ ≤ 1 := by
    have hd := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (F ψ) k).trans_lt (hOsub hψ.2)
    rw [hval ψ hψ.1.1 k] at hd
    change ‖4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) k ψ-1‖ < 1 at hd
    have he := norm_add_le (4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) k ψ-1) (1:ℂ)
    simp only [sub_add_cancel,norm_mul,norm_one] at he
    norm_num at he
    linarith
  simpa only [one_mul] using
    sourceComplexAction_le_gap_sq_of_normalized_bound ψ 1 (hfactor ψ hψ.1.2) hb n

/-- The exact Theorem 23.4 bound holds on a complex neighborhood of zero.
The spectral-height gap budget avoids division by the vanishing source norm. -/
theorem exists_zero_sourceM1Action_bound (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ (0:CoeffPair 2) ∈ V ∧ ∀ a ∈ V,
      Summable (sourceM1ActionTerm w (normalizedWeightedSource w a)) ∧
      (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a) n) ≤
        (2:ℝ)^21*sourceM1ActionScale w a := by
  obtain ⟨U,hU,h0U,hbound⟩ := exists_zero_sourceAction_gap_bound
  let V := (normalizedWeightedSource w ⁻¹' (U ∩ sourceSpectralStripNeighborhood (by simp))) ∩
    ball (0:CoeffPair 2) 1
  have hV : IsOpen V := ((hU.inter (isOpen_sourceSpectralStripNeighborhood (by simp))).preimage
    (continuous_normalizedWeightedSource w)).inter isOpen_ball
  have hz : normalizedWeightedSource w (0:CoeffPair 2) = 0 := (normalizedWeightedSourceCLM w).map_zero
  refine ⟨V,hV,⟨?_,mem_ball_self (by norm_num)⟩,?_⟩
  · change normalizedWeightedSource w 0 ∈ U ∩ sourceSpectralStripNeighborhood (by simp)
    rw [hz]
    exact ⟨h0U,real_mem_sourceSpectralStripNeighborhood (by simp) (by norm_num) 0
      (0:realTypeSourceSubmodule 2).property⟩
  intro a ha
  obtain ⟨hs,hb⟩ := sourceM1_complex_actions_summable_and_le w hw a ha.1.2 1 (by norm_num)
    (fun n => by simpa only [one_mul] using hbound _ ha.1.1 n)
  refine ⟨hs,hb.trans ?_⟩
  have hnorm : ‖a‖ < 1 := by simpa only [mem_ball,dist_zero_right] using ha.2
  have hq : ‖a‖^2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  have hcoef : 265*Real.pi^2*(1+‖a‖^2) ≤ (2:ℝ)^21 := by
    have hmul := mul_le_mul hpi (by linarith : 1+‖a‖^2 ≤ 2)
      (by positivity : 0 ≤ 1+‖a‖^2) (by norm_num : (0:ℝ) ≤ 16)
    norm_num
    nlinarith
  have h := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sq_nonneg (w.realExtension (16*‖a‖^2))) (sq_nonneg ‖a‖))
  simpa only [sourceM1ActionScale,one_mul,mul_assoc,mul_left_comm,mul_comm] using h

end NLS.ZakharovShabat
