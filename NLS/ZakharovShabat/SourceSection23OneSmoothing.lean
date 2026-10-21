import NLS.ZakharovShabat.SourceBirkhoffNativeRealRemainders
import NLS.ZakharovShabat.SourceSection23Original

/-! # One-smoothing for the retained original Section 23 family

The original actions, estimates, and solution theory coexist with both exact real one-smoothing maps for every positive integer order.
-/

noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- Section 23, including the exact real one-smoothing maps in both
directions, retaining the original Sections 17–22 family and estimates. -/
structure SourceSection23OneSmoothingData
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U : Set (CoeffPair 2)) : Prop extends SourceSection23Data D A B U where
  forward_analytic : ∀ m : ℕ, 1 ≤ m →
    AnalyticOnNhd ℝ (D.complex.nativeForwardFourierRemainder m) univ
  inverse_analytic : ∀ m : ℕ, 1 ≤ m →
    AnalyticOnNhd ℝ (D.complex.nativeInverseFourierRemainder m) univ
  forward_bounded : ∀ m : ℕ, 1 ≤ m → ∀ R : ℝ, 0 ≤ R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : weightedRealSourceSubmodule (p := 2)
      (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)), ‖a‖ ≤ R →
        ‖D.complex.nativeForwardFourierRemainder m a‖ ≤ C
  inverse_bounded : ∀ m : ℕ, 1 ≤ m → ∀ R : ℝ, 0 ≤ R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : originalRealSobolevTarget m, ‖z‖ ≤ R →
      ‖D.complex.nativeInverseFourierRemainder m z‖ ≤ C

/-- Add one-smoothing to any already retained Section 23 family without
rechoosing the map, roots, moment atlas, domains, or solution theory. -/
theorem SourceSection23Data.oneSmoothing
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection23Data D A B U) : SourceSection23OneSmoothingData D A B U :=
  ⟨Q,D.complex.nativeForwardFourierRemainder_analytic,
    D.complex.nativeInverseFourierRemainder_analytic,
    D.complex.nativeForwardFourierRemainder_uniform_ball,
    D.complex.nativeInverseFourierRemainder_uniform_ball⟩

/-- A single original family satisfies all named Section 23 estimates
and the real forward/inverse one-smoothing assertions at every positive
integer order, with its original actions and solution theory retained. -/
theorem sourceSection23_original_one_smoothing :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U : Set (CoeffPair 2), SourceSection23OneSmoothingData D A B U := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection23_original_estimates
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q.oneSmoothing⟩

end NLS.ZakharovShabat
