import NLS.ZakharovShabat.SourceBirkhoffSobolevEstimates

/-! # Remark 23.3: common constants in Theorems 23.1 and 23.2

All four estimates are packaged with a single positive pair of constants,
chosen before the potential. The physical norms and lower-order remainders
are exactly those of the two theorems.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Simultaneous Birkhoff and action estimates with the same constants. -/
structure SourceSobolevJointBounds {W₀ B W : Set (CoeffPair 2)}
    {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (c d : ℝ) : Prop where
  c_pos : 0 < c
  d_pos : 0 < d
  action_summable : ∀ a : realTypeHigherSobolevSourceLocus m,
    Summable (sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m)
  birkhoff_upper : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖D.sobolevCoordinates m hm m le_rfl a‖ ≤ c*
      (‖sourcePiSobolevCoordinates m m le_rfl a.val‖+
        (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(2*m)*‖higherSobolevSourceInclusion m a.val‖)
  birkhoff_lower : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ d*
      (‖D.sobolevCoordinates m hm m le_rfl a‖+
        (1+‖D.sobolevCoordinates m hm 1 hm a‖)^(4*m-3)*‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖)
  action_upper : ∀ a : realTypeHigherSobolevSourceLocus m,
    (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
      c^2*(‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2+
        (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*‖higherSobolevSourceInclusion m a.val‖^2)
  action_lower : ∀ a : realTypeHigherSobolevSourceLocus m,
    ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤ d^2*
      ((∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
        (1+∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n)^(4*m-3)*
          (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Every constructed Birkhoff map admits the shared positive constants in Remark 23.3. -/
theorem exists_sobolev_joint_bounds
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) : ∃ c d : ℝ, SourceSobolevJointBounds D m hm c d := by
  obtain ⟨cb,db,hcb,hdb,hB⟩ := D.exists_sobolev_two_sided_bounds m hm
  obtain ⟨ca,hca,hA⟩ := exists_sourceWeightedAction_sobolev_upper_bound m hm
  obtain ⟨da,hda,hL⟩ := exists_sourceSobolev_weightedAction_lower_bound m hm
  refine ⟨max cb ca,max db da,{
    c_pos := hcb.trans_le (le_max_left _ _)
    d_pos := hdb.trans_le (le_max_left _ _)
    action_summable := sourceWeightedAction_summable_on_Hm m hm
    birkhoff_upper := ?_
    birkhoff_lower := ?_
    action_upper := ?_
    action_lower := ?_ }⟩
  · intro a
    exact (hB a).1.trans (mul_le_mul_of_nonneg_right (le_max_left cb ca) (by positivity))
  · intro a
    exact (hB a).2.trans (mul_le_mul_of_nonneg_right (le_max_left db da) (by positivity))
  · intro a
    exact (hA a).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hca (le_max_right cb ca) 2) (by positivity))
  · intro a
    have hnon (k : ℕ) : 0 ≤ ∑' n : ℤ,
        sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ k n := by
      apply tsum_nonneg
      intro n
      unfold sourceWeightedActionTerm
      positivity
    exact (hL a).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hda (le_max_right db da) 2)
      (add_nonneg (hnon m) (mul_nonneg (pow_nonneg (by linarith [hnon 1]) _) (hnon 0))))

end SourceBirkhoffMapComplexData

/-- Theorems 23.1 and 23.2 with Remark 23.3's common constants, simultaneously
for one constructed map and every positive integer Sobolev order. -/
theorem exists_sourceBirkhoffMap_sobolev_common_constants :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
        ∀ m : ℕ, ∀ hm : 1 ≤ m, ∃ c d : ℝ, SourceSobolevJointBounds D m hm c d := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : (1:ℝ≥0∞) < 2)
  exact ⟨W₀,B,W,s,D,fun m hm => D.exists_sobolev_joint_bounds m hm⟩

end NLS.ZakharovShabat
