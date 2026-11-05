import NLS.SequenceSpaces.DeletedRealConjugation

/-! # A local inverse preserves the physical real subspace near zero -/
noncomputable section
open Set Metric
namespace NLS

theorem exists_real_preserving_inverse_neighborhood
    (F G : DeletedCoeff 2 0 → DeletedCoeff 2 0) (V W : Set (DeletedCoeff 2 0))
    (hV : IsOpen V) (hW : IsOpen W) (h0V : 0 ∈ V) (h0W : 0 ∈ W)
    (hF0 : F 0 = 0) (hG : ContinuousOn G W)
    (hinj : Set.InjOn F V) (hleft : ∀ a ∈ V, G (F a) = a)
    (hright : ∀ b ∈ W, G b ∈ V ∧ F (G b) = b)
    (η : ℝ) (hsub : V ⊆ ball (0 : DeletedCoeff 2 0) η)
    (hconj : ∀ a ∈ ball (0 : DeletedCoeff 2 0) η,
      F (deletedL2Conjugation a) = deletedL2Conjugation (F a)) :
    ∃ U : Set (DeletedCoeff 2 0), IsOpen U ∧ 0 ∈ U ∧ U ⊆ W ∧
      ∀ b ∈ U, deletedL2Conjugation b = b → deletedL2Conjugation (G b) = G b := by
  have hG0 : G 0 = 0 := by simpa only [hF0] using hleft 0 h0V
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let U : Set (DeletedCoeff 2 0) := W ∩ G ⁻¹' ball (0 : DeletedCoeff 2 0) δ
  refine ⟨U,hG.isOpen_inter_preimage hW isOpen_ball,⟨h0W,?_⟩,inter_subset_left,?_⟩
  · exact (show G (0 : DeletedCoeff 2 0) ∈ ball (0 : DeletedCoeff 2 0) δ by
      rw [hG0]
      exact mem_ball_self hδ)
  · intro b hb hJb
    obtain ⟨hGb,hFGb⟩ := hright b hb.1
    have hJGb : deletedL2Conjugation (G b) ∈ V := by
      apply hδV
      rw [mem_ball_zero_iff,norm_deletedL2Conjugation]
      exact mem_ball_zero_iff.mp hb.2
    apply hinj hJGb hGb
    rw [hconj (G b) (hsub hGb),hFGb,hJb]

end NLS
