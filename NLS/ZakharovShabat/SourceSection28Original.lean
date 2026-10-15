import NLS.ZakharovShabat.SourceSection28WeightedActions
import NLS.ZakharovShabat.SourceSection28SignedIndex

/-! # Section 28 for one retained original family

The same original actions and Birkhoff family support (5.14), (5.15),
the final bounds in Lemma 28.1 and Proposition 28.2, and Theorem 23.4.
A single connected L²-open restriction S is chosen before all weights.
The literal signed ratio is separately refuted at the actual zero source.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- One original family and one common complex source neighborhood for Section 28. -/
structure SourceSection28Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U T S : Set (CoeffPair 2)) : Prop extends SourceSection27Data D A B U T where
  action_gap_open : IsOpen S
  action_gap_connected : IsConnected S
  action_gap_real_subset : realTypeSourceLocus 2 ⊆ S
  action_gap_subset : S ⊆ T
  action_gap_strip : S ⊆ sourceSpectralStripNeighborhood (by simp)
  critical_coordinate : ∀ ψ ∈ S, ∀ n : ℤ,
    ‖sourceActionCriticalCoordinate (by simp) (by norm_num) n ψ‖ ≤ 2
  chi_action_bound : ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
    normalizedWeightedSource w a ∈ S → ∀ n : ℤ, 8*‖a‖^2 ≤ 1+|(n:ℝ)| →
      (∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (normalizedWeightedSource w a) n,
        ‖sourceActionChi (by simp) (by norm_num) n (normalizedWeightedSource w a) z‖ ≤ 2048*(1+‖a‖^2)) ∧
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
        4608*(1+‖a‖^2)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w a) n‖^2
  weighted_continuous : ∀ w : SpectralWeight, w.HasLinearFactor →
    ContinuousOn (fun a : CoeffPair 2 => ∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖)
      (normalizedWeightedSource w ⁻¹' S)
  weighted_bound : ∀ w : SpectralWeight, w.HasLinearFactor →
    ∃ R : Set (CoeffPair 2), IsOpen R ∧ IsConnected R ∧ realTypeSourceLocus 2 ⊆ R ∧
      (∀ a ∈ R, normalizedWeightedSource w a ∈ S) ∧ ∀ a ∈ R,
        Summable (fun n : ℤ => (w (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
        (∑' n : ℤ, (w (2*n))^2*‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
          (2:ℝ)^21*(w.realExtension (16*‖a‖^2))^2*‖a‖^2

/-- Retain all preceding data and choose the single Section 28 source restriction. -/
theorem SourceSection27Data.section28
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection27Data D A B U T) :
    ∃ S : Set (CoeffPair 2), SourceSection28Data D A B U T S := by
  obtain ⟨S,hS,hconn,hrS,hST,hstrip,hcrit,hb⟩ := Q.section28_original_chi_neighborhood
  exact ⟨S,Q,hS,hconn,hrS,hST,hstrip,hcrit,hb,
    Q.section28_weighted_continuousOn S hST hstrip,Q.section28_weighted_neighborhood S hS hrS hST⟩

namespace SourceSection28Data
variable {W₀ W V Wa B U T S : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- The local ℓ² assertion (5.14) uses the original filled normalized actions. -/
theorem normalized_locally_uniform (Q : SourceSection28Data D A B U T S) (φ : CoeffPair 2) (hφ : φ ∈ S) :
    ∃ O : Set (CoeffPair 2), IsOpen O ∧ φ ∈ O ∧ O ⊆ S ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ O, ∃ b : Coeff 2,
        (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n ψ-1) ∧ ‖b‖ ≤ C := by
  have hφW₀ := D.previous.previous.previous.subset
    (D.complex.source_subset (Q.original_subset (Q.gap_subset (Q.action_gap_subset hφ))))
  obtain ⟨O,hO,hφO,_,C,hC,hb⟩ := D.section28_originalEstimates.section28_locally_uniform φ hφW₀
  exact ⟨O ∩ S,hO.inter Q.action_gap_open,⟨hφO,hφ⟩,inter_subset_right,C,hC,fun ψ hψ => hb ψ hψ.1⟩

/-- The H¹-uniform conclusion following (5.14) has one bound before all sources in the ball. -/
theorem normalized_uniform_H1_ball (Q : SourceSection28Data D A B U T S) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∃ b : Coeff 2, (∀ n : ℤ, b n = 4*sourceNormalizedIndexedAction (by simp) (by norm_num) n
        (sobolevSourceInclusion a.val)-1) ∧ ‖b‖ ≤ C := by
  apply D.section28_originalEstimates.section28_uniform_physical_H1_ball _ R
  intro φ hφ
  exact D.previous.previous.previous.subset (D.complex.source_subset (Q.original_subset (Q.real_subset hφ)))

/-- The weighted sum converges on the entire weighted part of S, not just its estimate neighborhood. -/
theorem weighted_summable (Q : SourceSection28Data D A B U T S)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (ha : normalizedWeightedSource w a ∈ S) :
    Summable (fun n : ℤ => (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) :=
  (D.section28_originalEstimates.section28_weighted_summable_continuousAt w hw a
    (D.previous.previous.previous.subset (D.complex.source_subset
      (Q.original_subset (Q.gap_subset (Q.action_gap_subset ha))))) (Q.action_gap_strip ha)).1

/-- The actual χ bound and original action bound in the exact physical H¹ norm. -/
theorem physical_H1_bounds (Q : SourceSection28Data D A B U T S)
    (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ S) :
    (∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ 1+|(n:ℝ)| →
      ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (sobolevSourceInclusion a) n,
        ‖sourceActionChi (by simp) (by norm_num) n (sobolevSourceInclusion a) z‖ ≤
          2048*(1+‖sourcePhysicalH1Coordinates a‖^2)) ∧
    (∀ n : ℤ, 8*‖sourcePhysicalH1Coordinates a‖^2 ≤ |(n:ℝ)| →
      ‖sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion a)‖ ≤
        4608*(1+‖sourcePhysicalH1Coordinates a‖^2)*
          ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) n‖^2) := by
  have h := Q.chi_action_bound (SpectralWeight.piSobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) (sourcePhysicalH1Coordinates a)
    (by simpa only [normalizedWeightedSource_physicalH1Coordinates] using ha)
  simp only [normalizedWeightedSource_physicalH1Coordinates] at h
  exact ⟨fun n hn => (h n hn).1,fun n hn => (h n (by linarith)).2⟩

/-- Formula (5.15) for any source of the common domain and any bound on its closed gap. -/
theorem normalized_bound (Q : SourceSection28Data D A B U T S) (ψ : CoeffPair 2) (hψ : ψ ∈ S)
    (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n,
      ‖sourceActionChi (by simp) (by norm_num) n ψ z‖ ≤ K) :
    ‖4*sourceNormalizedIndexedAction (by simp) (by norm_num) n ψ‖ ≤ 9*K :=
  D.section28_gapFormulas.section28_normalized_bound ψ
    (D.previous.previous.previous.subset (D.complex.source_subset
      (Q.original_subset (Q.gap_subset (Q.action_gap_subset hψ))))) n K hK (Q.critical_coordinate ψ hψ n) hb

end SourceSection28Data

/-- One original family carries the complete valid Section 28 estimates and domain restrictions. -/
theorem sourceSection28_original :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U T S : Set (CoeffPair 2), SourceSection28Data D A B U T S := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,T,Q⟩ := sourceSection27_original
  obtain ⟨S,hS⟩ := Q.section28
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,T,S,hS⟩

end NLS.ZakharovShabat
