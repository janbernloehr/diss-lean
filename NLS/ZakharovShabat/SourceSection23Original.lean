import NLS.ZakharovShabat.SourceSection23Sobolev
import NLS.ZakharovShabat.SourceSection23Weighted
import NLS.SequenceSpaces.SpectralWeightGrowth

/-! # Section 23 estimates for one retained original Birkhoff family

The original family is chosen once before all integer orders, real orders,
weights, and potentials. Weighted complex neighborhoods retain the source
domain and all original indexed actions.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The four named estimate results of Section 23, retaining Sections 17–22. -/
structure SourceSection23Data
    {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    {Wa : Set (CoeffPair 2)} (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s)
    (B U : Set (CoeffPair 2)) : Prop extends SourceSection20Data D A B U where
  sobolev : ∀ m : ℕ, ∀ hm : 1 ≤ m, ∃ c d : ℝ, SourceSection23SobolevBounds D m hm c d
  weighted : ∀ w : SpectralWeight, ∀ hw : w.HasLinearFactor,
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
        (∀ a ∈ T, normalizedWeightedSource w a ∈ U) ∧
        (∀ a ∈ T,
          Summable (fun n : ℤ => (w (2*n))^2*
            ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
          (∑' n : ℤ, (w (2*n))^2*
            ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
              (2048:ℝ)^2*(w.realExtension (16*‖a‖^2))^2*‖a‖^2) ∧
        ∀ a : realTypeSourceSubmodule 2,
          ‖D.complex.m1Coordinates w hw a‖ ≤ 2048*w.realExtension (16*‖a.val‖^2)*‖a.val‖
  realSobolev : ∀ r : ℝ, ∀ hr : 1 ≤ r,
      ∃ T : Set (CoeffPair 2), IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
        (∀ a ∈ T, sourceRealSobolevInclusion r (zero_le_one.trans hr) a ∈ U) ∧
        (∀ a ∈ T,
          Summable (fun n : ℤ => (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r)*
            ‖sourceIndexedAction (by simp) (by norm_num) n
              (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ∧
          (∑' n : ℤ, (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r)*
            ‖sourceIndexedAction (by simp) (by norm_num) n
              (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ≤
            (realSobolevEstimateConstant r)^2*(1+‖a‖)^(4*r)*‖a‖^2) ∧
        ∀ a : realTypeSourceSubmodule 2,
          ‖D.complex.realSobolevCoordinates r hr a‖ ≤
            realSobolevEstimateConstant r*(1+‖a.val‖)^(2*r)*‖a.val‖

/-- Add all estimates to the already chosen original family without changing its domain. -/
theorem SourceSection20Data.section23
    {W₀ W V Wa B U : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection20Data D A B U) : SourceSection23Data D A B U :=
  ⟨Q,D.section23_sobolev_bounds,Q.section23_weighted_neighborhood,Q.section23_realSobolev_neighborhood⟩

/-- One original map satisfies all integer, weighted, and real-order estimates.
No independent map or action family is chosen for any order or weight. -/
theorem sourceSection23_original_estimates :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U : Set (CoeffPair 2), SourceSection23Data D A B U := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q,_,_,_,_,_,_⟩ :=
    sourceSection22_original (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q.section23⟩
end NLS.ZakharovShabat
