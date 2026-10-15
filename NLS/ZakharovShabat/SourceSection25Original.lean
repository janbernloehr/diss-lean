import NLS.ZakharovShabat.SourceSection25Localization
import NLS.ZakharovShabat.SourceSection25Coefficients
import NLS.ZakharovShabat.SourceSection25Gaps

/-! # Section 25 for one retained original family

The original family and its Section 24 domain U are unchanged. One open
subdomain T containing every real source supports the global weighted gap
estimate for all M₁ weights. The localization and tail estimates in the
imported modules hold at every complex source of the stated regularity.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The retained original family together with one weight-independent gap domain. -/
structure SourceSection25Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U T : Set (CoeffPair 2)) : Prop extends SourceSection24Data D A B U where
  gap_open : IsOpen T
  gap_real_subset : realTypeSourceLocus 2 ⊆ T
  gap_subset : T ⊆ U
  gap_bound : ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
    normalizedWeightedSource w a ∈ T →
    Summable (fun n : ℤ => (w (2*n)*‖sourcePeriodicGapDisplacement
      (by simp) (by norm_num) (normalizedWeightedSource w a) n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖sourcePeriodicGapDisplacement
      (by simp) (by norm_num) (normalizedWeightedSource w a) n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖a‖^2))^2*(1+‖a‖^2)*‖a‖^2

/-- Add the common gap neighborhood while retaining the original family and domain. -/
theorem SourceSection24Data.section25
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection24Data D A B U) :
    ∃ T : Set (CoeffPair 2), SourceSection25Data D A B U T := by
  obtain ⟨T,hT,hr,hs,hb⟩ := Q.section25_gap_neighborhood
  exact ⟨T,Q,hT,hr,hs,hb⟩

/-- All original real weighted sources belong to the common gap domain. -/
theorem SourceSection25Data.real_weighted_mem
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection25Data D A B U T) (w : SpectralWeight) (a : realTypeSourceSubmodule 2) :
    normalizedWeightedSource w a.val ∈ T :=
  Q.gap_real_subset (normalizedWeightedSource_realType w a.val a.property)

/-- One original family and one complex gap domain are chosen before all weights and sources. -/
theorem sourceSection25_original :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U T : Set (CoeffPair 2), SourceSection25Data D A B U T := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection24_original
  obtain ⟨T,hT⟩ := Q.section25
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,T,hT⟩
end NLS.ZakharovShabat
