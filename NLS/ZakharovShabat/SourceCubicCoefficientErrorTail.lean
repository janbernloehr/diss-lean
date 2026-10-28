import NLS.ZakharovShabat.SourceCubicCoefficientError

/-! # The combined infinite fourth-power error tail

These statements concern original period-two coefficients, actual whole-strip
suprema and infinite signed sums. The final source inequality still requires
the asymptotics of the actual counted-root gap; it is not resolved here.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicCoefficientErrorTailFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The signed fourth-power tail, with its cutoff boundary retained. -/
def cubicFourthPowerTail (N : ℕ) (f : ℤ → ℝ) (m : ℤ) : ℝ := if N ≤ m.natAbs then (f m)^4 else 0

/-- The fourth-power tail agrees with the earlier real-power source tail at p=4. -/
theorem cubicFourthPowerTail_eq (N : ℕ) (f : ℤ → ℝ) : cubicFourthPowerTail N f = sourceCoefficientPowerTail 4 N f := by
  funext m
  simp only [cubicFourthPowerTail,sourceCoefficientPowerTail,ENNReal.toReal_ofNat,Real.rpow_ofNat]

/-- The higher error tail is summable under the global smallness condition. -/
theorem sourceCubicHigherErrorSup_summable (n : ℤ) (s : ℝ) (N : ℕ) (hN : 0 < N) (positive : Bool)
    (hsmall : SourceCubicSmall n s) : Summable (cubicFourthPowerTail N (fun m => sourceCubicHigherErrorSup n s m positive)) := by
  rw [cubicFourthPowerTail_eq]
  exact (resonantCubicErrorSup_tail (p := 4) (by simp) (by norm_num) SpectralWeight.one
      (weightedCubicTailFamily n s) N hN hsmall positive).1

/-- The cubic perturbation has a summable fourth-power tail. -/
theorem sourceCubicPerturbationSup_summable (n : ℤ) (hn : 0 < n) (s : ℝ) (N : ℕ) (positive : Bool) :
    Summable (cubicFourthPowerTail N (fun m => sourceCubicPerturbationSup n s m positive)) := by
  cases positive <;> exact resonantCubicPerturbationSup_fourth_summable (by simp) SpectralWeight.one
    (sourceCubicBackgroundProfile n) (sourceCubicResonantProfile n) n (s : ℂ) _ _ (twoModeResonantPotential_cubicSupport SpectralWeight.one n hn 1)
    (singleResonantPotential_cubicSupport SpectralWeight.one n hn.le _ _) (by decide) N

/-- The fourth power of a sum is bounded by eight times the sum of fourth powers. -/
private theorem cubicFourth_add_le (a b : ℝ) : (a+b)^4 ≤ 8*a^4+8*b^4 := by
  calc
    _ = ((a+b)^2)^2 := by ring
    _ ≤ (2*(a^2+b^2))^2 := pow_le_pow_left₀ (sq_nonneg _)
      (by nlinarith [sq_nonneg (a-b)]) 2
    _ ≤ _ := by nlinarith [sq_nonneg (a^2-b^2)]

/-- The combined error has a summable fourth-power tail controlled by its two components. -/
theorem sourceCubicCombinedError_summable_bound (n : ℤ) (hn : 0 < n) (s : ℝ) (N : ℕ) (hN : 0 < N)
    (positive : Bool) (hsmall : SourceCubicSmall n s) :
    Summable (cubicFourthPowerTail N (fun m => sourceCubicCombinedError n s m positive)) ∧
    (∑' m, cubicFourthPowerTail N (fun m => sourceCubicCombinedError n s m positive) m) ≤
      8*(∑' m, cubicFourthPowerTail N (fun m => sourceCubicHigherErrorSup n s m positive) m)+
      8*(∑' m, cubicFourthPowerTail N (fun m => sourceCubicPerturbationSup n s m positive) m) := by
  have hH := sourceCubicHigherErrorSup_summable n s N hN positive hsmall
  have hP := sourceCubicPerturbationSup_summable n hn s N positive
  have hnon (m : ℤ) : 0 ≤ cubicFourthPowerTail N (fun m => sourceCubicCombinedError n s m positive) m := by
    unfold cubicFourthPowerTail
    split_ifs <;> positivity
  have hdom (m : ℤ) : cubicFourthPowerTail N (fun m => sourceCubicCombinedError n s m positive) m ≤
      8*cubicFourthPowerTail N (fun m => sourceCubicHigherErrorSup n s m positive) m+8*cubicFourthPowerTail N (fun m => sourceCubicPerturbationSup n s m positive) m := by
    unfold cubicFourthPowerTail
    split_ifs
    · exact cubicFourth_add_le _ _
    · norm_num
  have hs := ((hH.mul_left 8).add (hP.mul_left 8)).of_nonneg_of_le hnon hdom
  refine ⟨hs,?_⟩
  have h := hs.tsum_le_tsum hdom ((hH.mul_left 8).add (hP.mul_left 8))
  simpa only [(hH.mul_left 8).tsum_add (hP.mul_left 8),tsum_mul_left] using h

/-- The normalized higher error tail tends to zero. -/
theorem sourceCubicHigherErrorSup_tail_tendsto (n : ℤ) (N : ℕ) (hN : 0 < N) (positive : Bool) :
    Tendsto (fun s : ℝ => (∑' m, cubicFourthPowerTail N (fun m => sourceCubicHigherErrorSup n s m positive) m)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [resonantCubicFourthErrorSum,sourceCoefficientPowerTail,sourceCubicHigherErrorSup,cubicFourthPowerTail,
    ENNReal.toReal_ofNat,Real.rpow_ofNat,unitWeightedPairEquiv_sourceCubicTailFamily] using
    sourceCubicTailFamily_normalized_tail_tendsto n N hN positive

/-- The normalized cubic perturbation tail tends to zero. -/
theorem sourceCubicPerturbationSup_tail_tendsto (n : ℤ) (hn : 0 < n) (N : ℕ) (positive : Bool) :
    Tendsto (fun s : ℝ => (∑' m, cubicFourthPowerTail N (fun m => sourceCubicPerturbationSup n s m positive) m)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  cases positive <;> exact sourceCubicTailFamily_cubic_perturbation_tail n hn N _ _ (by decide)

/-- The normalized combined infinite error tail tends to zero. -/
theorem sourceCubicCombinedError_tail_tendsto (n : ℤ) (hn : 0 < n) (N : ℕ) (hN : 0 < N) (positive : Bool) :
    Tendsto (fun s : ℝ => (∑' m, cubicFourthPowerTail N (fun m => sourceCubicCombinedError n s m positive) m)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu := ((sourceCubicHigherErrorSup_tail_tendsto n N hN positive).const_mul 8).add
    ((sourceCubicPerturbationSup_tail_tendsto n hn N positive).const_mul 8)
  simp only [mul_zero,add_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun s => div_nonneg (tsum_nonneg (by
    intro m
    unfold cubicFourthPowerTail
    split_ifs <;> positivity)) (by positivity))) ?_ hu
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,self_mem_nhdsWithin] with s hs hspos
  have h := div_le_div_of_nonneg_right (sourceCubicCombinedError_summable_bound n hn s N hN positive hs.1).2
    (pow_nonneg hspos.le 12)
  simpa only [add_div,mul_div_assoc] using h

end NLS.ZakharovShabat
