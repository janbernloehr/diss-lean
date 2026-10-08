import NLS.ZakharovShabat.SourceM1ActionNearZero

/-! # Theorem 23.4: the complex neighborhood weighted action estimate -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Doubling the real bound gives the source constant 2²¹ on a neighborhood
of every real weighted potential. The zero potential is included separately. -/
theorem exists_local_sourceM1Action_bound (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ a.val ∈ V ∧ ∀ b ∈ V,
      Summable (sourceM1ActionTerm w (normalizedWeightedSource w b)) ∧
      (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w b) n) ≤
        (2:ℝ)^21*sourceM1ActionScale w b := by
  by_cases ha : a.val = 0
  · simpa only [ha] using exists_zero_sourceM1Action_bound w hw
  have hscale : 0 < sourceM1ActionScale w a.val :=
    mul_pos (sq_pos_of_pos (w.realExtension_pos _)) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr ha))
  have hr := (sourceM1_real_weighted_actions_normalized w hw a).2
  have hstrict : (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a.val) n) -
      (2:ℝ)^21*sourceM1ActionScale w a.val < 0 := by
    have hr' : (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a.val) n) ≤
        (2:ℝ)^20*sourceM1ActionScale w a.val := by
      simpa only [sourceM1ActionScale,mul_assoc] using hr
    norm_num at hr' ⊢
    linarith
  have hc := (continuousAt_sourceM1ActionTotal w hw a).sub
    ((continuous_sourceM1ActionScale w).continuousAt.const_mul ((2:ℝ)^21))
  have hnear := hc.eventually (gt_mem_nhds hstrict)
  obtain ⟨O,hOsub,hO,haO⟩ := mem_nhds_iff.mp hnear
  obtain ⟨U,hU,haU,_,_,hdata⟩ := exists_local_sourceM1Action_continuousMap w hw a
  refine ⟨U ∩ O,hU.inter hO,⟨haU,haO⟩,?_⟩
  intro b hb
  refine ⟨(hdata b hb.1).1,?_⟩
  have h := hOsub hb.2
  dsimp at h
  linarith

/-- The weighted complex action estimate on one open neighborhood of the
entire real weighted source space, with the printed constant 2²¹. -/
theorem exists_sourceM1Action_neighborhood (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ realTypeSourceLocus 2 ⊆ V ∧ ∀ a ∈ V,
      Summable (sourceM1ActionTerm w (normalizedWeightedSource w a)) ∧
      (∑' n : ℤ, sourceM1ActionTerm w (normalizedWeightedSource w a) n) ≤
        (2:ℝ)^21*(w.realExtension (16*‖a‖^2))^2*‖a‖^2 := by
  classical
  choose U hU haU hbound using exists_local_sourceM1Action_bound w hw
  refine ⟨⋃ a : realTypeSourceSubmodule 2, U a,isOpen_iUnion hU,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haU _⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact ⟨(hbound a b ha).1,by
      simpa only [sourceM1ActionScale,mul_assoc] using (hbound a b ha).2⟩

end NLS.ZakharovShabat
