import NLS.ZakharovShabat.SourceWeightedHigherActionBound
import NLS.ZakharovShabat.SourceSobolevGapBound

/-! # Absolute convergence of the first three higher-action levels on H¹

The weighted squared-gap estimate dominates the actual complex higher
actions. One complex H¹ neighborhood and one ℓ¹ bound work for levels
one through three, without a finite-gap assumption.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem higherAction_sobolev_weight_bound (n : ℤ) (k : ℕ) (hk : k ≤ 2) :
    (1+|(n:ℝ)|)^k ≤ ((SpectralWeight.sobolev 1 (by norm_num)) (2*n))^2 := by
  calc
    _ ≤ (1+|(n:ℝ)|)^2 := pow_le_pow_right₀ (by linarith [abs_nonneg (n:ℝ)]) hk
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      simp only [SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
        Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_nonneg (n:ℝ)]

/-- Actual higher-action sequences have uniformly bounded ℓ¹ realizations
near every real H¹ source, simultaneously through the physical energy level. -/
theorem exists_local_sourceSobolevHigherAction_bound
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∀ k : ℕ, k ≤ 2 → ∃ J : Coeff 1,
        (∀ n : ℤ, J n = sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) ∧
        ‖J‖ ≤ C :=
  exists_local_sourceWeightedHigherAction_bound (SpectralWeight.sobolev 1 (by norm_num))
    sobolevSourceInclusion sobolevSourceWeightedPeriodOne
    weightedBaseToPair_sobolevSourceWeightedPeriodOne 2
    higherAction_sobolev_weight_bound a ha

/-- On a common complex H¹ neighborhood, the first three defining
higher-action series are absolutely convergent. -/
theorem exists_local_sourceSobolevHigherAction_summable
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∀ b ∈ U, ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
        sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) := by
  obtain ⟨U,hU,haU,C,hbound⟩ := exists_local_sourceSobolevHigherAction_bound a ha
  refine ⟨U,hU,haU,?_⟩
  intro b hb k hk
  obtain ⟨J,hJ,_⟩ := hbound b hb k hk
  exact J.property.summable_of_one.congr hJ

end NLS.ZakharovShabat
