import NLS.ZakharovShabat.SourceSection28GapBounds
import NLS.ZakharovShabat.SourceSection28WeightedContinuity
import NLS.ZakharovShabat.SourceM1ActionNeighborhood

/-! # Original weighted actions in the proof of Theorem 23.4

The real constant 2²⁰ and complex constant 2²¹ use the same indexed actions.
The weighted complex neighborhoods are connected and decode into the
retained common L² domain. Continuity holds on its whole weighted part.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The printed 2²¹ action constant inside any retained original subdomain. -/
theorem SourceSection27Data.section28_weighted_neighborhood
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection27Data D A B U T) (S : Set (CoeffPair 2))
    (hS : IsOpen S) (hrS : realTypeSourceLocus 2 ⊆ S) (hST : S ⊆ T)
    (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∃ R : Set (CoeffPair 2), IsOpen R ∧ IsConnected R ∧ realTypeSourceLocus 2 ⊆ R ∧
      (∀ a ∈ R, normalizedWeightedSource w a ∈ S) ∧
      ∀ a ∈ R,
        Summable (fun n : ℤ => (w (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
        (∑' n : ℤ, (w (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
            (2:ℝ)^21*(w.realExtension (16*‖a‖^2))^2*‖a‖^2 := by
  obtain ⟨O,hO,hrO,hb⟩ := exists_sourceM1Action_neighborhood w hw
  let X := O ∩ (normalizedWeightedSource w) ⁻¹' S
  have hX : IsOpen X := hO.inter (hS.preimage (continuous_normalizedWeightedSource w))
  have hrX : realTypeSourceLocus 2 ⊆ X := fun a ha =>
    ⟨hrO ha,hrS (normalizedWeightedSource_realType w a ha)⟩
  let R := connectedComponentIn X (0 : CoeffPair 2)
  have hRX : R ⊆ X := connectedComponentIn_subset X 0
  have hz : (0 : CoeffPair 2) ∈ realTypeSourceLocus 2 := by simp [realTypeSourceLocus]
  refine ⟨R,hX.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrX hz),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz hrX,
    fun a ha => (hRX ha).2,?_⟩
  intro a ha
  have he (n : ℤ) := D.indexed_action_eq_complex (normalizedWeightedSource w a)
    (Q.original_subset (Q.gap_subset (hST (hRX ha).2))) n
  simp_rw [he]
  exact hb a (hRX ha).1

/-- The real 2²⁰ estimate uses the same original indexed actions. -/
theorem section28_real_weighted_action_bound (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    Summable (fun n : ℤ => (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a.val)‖) ∧
    (∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a.val)‖) ≤
        (2:ℝ)^20*(w.realExtension (16*‖a.val‖^2))^2*‖a.val‖^2 := by
  have hr := normalizedWeightedSource_realType w a.val a.property
  have he (n : ℤ) : sourceM1ActionTerm w (normalizedWeightedSource w a.val) n =
      (w (2*n))^2*‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a.val)‖ := by
    simp only [sourceM1ActionTerm,
      sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) _ _ hr,
      sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) _ _ hr]
  obtain ⟨hs,hb⟩ := sourceM1_real_weighted_actions_normalized w hw a
  exact ⟨hs.congr he,by simpa only [he] using hb⟩

/-- The literal weighted sum is continuous throughout the weighted part of the retained domain. -/
theorem SourceSection27Data.section28_weighted_continuousOn
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection27Data D A B U T) (S : Set (CoeffPair 2)) (hST : S ⊆ T)
    (hstrip : S ⊆ sourceSpectralStripNeighborhood (by simp))
    (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ContinuousOn (fun a : CoeffPair 2 => ∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖)
      (normalizedWeightedSource w ⁻¹' S) := by
  intro a ha
  exact (D.section28_originalEstimates.section28_weighted_continuousAt w hw a
    (D.previous.previous.previous.subset (D.complex.source_subset (Q.original_subset (Q.gap_subset (hST ha)))))
    (hstrip ha)).continuousWithinAt

end NLS.ZakharovShabat
