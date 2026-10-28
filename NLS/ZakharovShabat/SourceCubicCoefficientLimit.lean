import NLS.ZakharovShabat.SourceCubicCoefficientErrorTail
import NLS.SequenceSpaces.FourthPowerSingleLimit

/-! # The normalized original coefficient supremum sum

These statements concern original period-two coefficients, actual whole-strip
suprema and infinite signed sums. The final source inequality still requires
the asymptotics of the actual counted-root gap; it is not resolved here.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicCoefficientLimitFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- Restrict a sequence to the signed tail and divide by the cubic amplitude. -/
def cubicFourthNormalizedTail (N : ℕ) (s : ℝ) (f : ℤ → ℝ) (m : ℤ) : ℝ :=
  if N ≤ m.natAbs then f m/s^3 else 0

/-- Taking the fourth power converts cubic normalization to division by s^12. -/
theorem cubicFourthNormalizedTail_pow (N : ℕ) (s : ℝ) (f : ℤ → ℝ) (m : ℤ) :
    (cubicFourthNormalizedTail N s f m)^4 = cubicFourthPowerTail N f m/s^12 := by
  unfold cubicFourthNormalizedTail cubicFourthPowerTail
  split_ifs <;> norm_num [div_pow,← pow_mul]

/-- Normalization commutes with the entire fourth-power sum. -/
theorem cubicFourthNormalizedTail_sum (N : ℕ) (s : ℝ) (f : ℤ → ℝ) :
    (∑' m, (cubicFourthNormalizedTail N s f m)^4) = (∑' m, cubicFourthPowerTail N f m)/s^12 := by
  simp_rw [cubicFourthNormalizedTail_pow]
  exact tsum_div_const

/-- Both actual error suprema are nonnegative for small positive amplitude. -/
theorem sourceCubicCombinedError_nonneg (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hsmall : SourceCubicSmall n s) : 0 ≤ sourceCubicCombinedError n s m positive :=
  add_nonneg (sourceCubicHigherErrorSup_bounds n s m positive hsmall).1 (sourceCubicPerturbationSup_bounds n s m positive hs hs1).1

/-- A positive target index lies below the absolute value of every tail index. -/
theorem sourceCubicTail_abs_index (n m : ℤ) (hn : 0 < n) (hm : n.natAbs ≤ m.natAbs) : n ≤ |m| := by
  have h : (n.natAbs : ℤ) ≤ (m.natAbs : ℤ) := by exact_mod_cast hm
  simpa only [Int.natCast_natAbs,abs_of_pos hn] using h

/-- The normalized actual supremum sequence approaches a single background contribution with summable fourth-power error. -/
theorem sourceCubicRemainderSup_normalized_bounds (n : ℤ) (hn : 0 < n) (s : ℝ) (positive : Bool)
    (hs : 0 < s) (hs1 : s ≤ 1) (hsmall : SourceCubicSmall n s) :
    (∀ m, 0 ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive) m) ∧
    (∀ m, 0 ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m) ∧
    (∀ m, |cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive) m-
      (if m=n then sourceCubicBackgroundScale n else 0)| ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m) ∧
    Summable (fun m => (cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m)^4) := by
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  refine ⟨?_,?_,?_,?_⟩
  · intro m
    unfold cubicFourthNormalizedTail
    split_ifs with hm
    · exact div_nonneg (sourceCubicRemainderSup_bounds n m hn (sourceCubicTail_abs_index n m hn hm) s hs.le hs1 hsmall positive).1
        (pow_nonneg hs.le 3)
    · exact le_rfl
  · intro m
    unfold cubicFourthNormalizedTail
    split_ifs
    · exact div_nonneg (sourceCubicCombinedError_nonneg n s m positive hs.le hs1 hsmall) (pow_nonneg hs.le 3)
    · exact le_rfl
  · intro m
    unfold cubicFourthNormalizedTail
    by_cases hm : n.natAbs ≤ m.natAbs
    · simp only [if_pos hm]
      have hb := (sourceCubicRemainderSup_bounds n m hn (sourceCubicTail_abs_index n m hn hm) s hs.le hs1 hsmall positive).2
      have he : sourceCubicRemainderSup n s m positive/s^3-(if m=n then sourceCubicBackgroundScale n else 0) =
          (sourceCubicRemainderSup n s m positive-(if m=n then s^3*sourceCubicBackgroundScale n else 0))/s^3 := by
        rw [sub_div]
        congr 1
        split_ifs <;> simp [hs.ne']
      rw [he,abs_div,abs_of_pos (pow_pos hs 3)]
      exact div_le_div_of_nonneg_right hb (pow_nonneg hs.le 3)
    · have hmn : m ≠ n := by intro h; subst m; exact hm le_rfl
      simp [hm,hmn]
  · have h := (sourceCubicCombinedError_summable_bound n hn s n.natAbs hN positive hsmall).1.div_const (s^12)
    simpa only [cubicFourthNormalizedTail_pow] using h

/-- The actual original remainder supremum sum divided by s^12 tends to the exact background fourth power. -/
theorem sourceCubicRemainderSup_sum_normalized_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool) :
    Tendsto (fun s : ℝ => (∑' m, cubicFourthPowerTail n.natAbs (fun m => sourceCubicRemainderSup n s m positive) m)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 ((sourceCubicBackgroundScale n)^4)) := by
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  have he : Tendsto (fun s : ℝ => ∑' m, (cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m)^4)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [cubicFourthNormalizedTail_sum] using sourceCubicCombinedError_tail_tendsto n hn n.natAbs hN positive
  have hb : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∀ m, 0 ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive) m) ∧
      (∀ m, 0 ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m) ∧
      (∀ m, |cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive) m-
        (if m=n then sourceCubicBackgroundScale n else 0)| ≤ cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m) ∧
      Summable (fun m => (cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive) m)^4) := by
    have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin]
      with s hsmall hs1 hs
    exact sourceCubicRemainderSup_normalized_bounds n hn s positive hs hs1.le hsmall.1
  simpa only [cubicFourthNormalizedTail_sum] using fourthPowerSum_tendsto_single
    (fun s => cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive))
    (fun s => cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive)) n (sourceCubicBackgroundScale n) hb he

/-- The actual original remainder fourth-power tail is summable for small positive amplitude. -/
theorem sourceCubicRemainderSup_fourth_summable (n : ℤ) (hn : 0 < n) (s : ℝ) (positive : Bool)
    (hs : 0 < s) (hs1 : s ≤ 1) (hsmall : SourceCubicSmall n s) :
    Summable (cubicFourthPowerTail n.natAbs (fun m => sourceCubicRemainderSup n s m positive)) := by
  have hb := sourceCubicRemainderSup_normalized_bounds n hn s positive hs hs1 hsmall
  have h := (fourthPowerSum_bounds_single
    (cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicRemainderSup n s m positive))
    (cubicFourthNormalizedTail n.natAbs s (fun m => sourceCubicCombinedError n s m positive)) n (sourceCubicBackgroundScale n)
    hb.1 hb.2.2.1 hb.2.2.2).1.mul_right (s^12)
  simpa only [cubicFourthNormalizedTail_pow,div_mul_cancel₀ _ (pow_ne_zero 12 hs.ne')] using h

end NLS.ZakharovShabat
