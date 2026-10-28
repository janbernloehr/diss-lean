import NLS.ZakharovShabat.SourceCubicPrintedSumLimit

/-! # Original coefficients at moving spectral parameters

Supporting estimates for the unresolved final weighted gap sum on p.44.
The actual counted-root gap still needs comparison with the coefficient sum.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicMovingCoefficientFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The combined target-strip error vanishes after cubic normalization. -/
theorem sourceCubicCombinedError_normalized_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool) :
    Tendsto (fun s : ℝ => sourceCubicCombinedError n s n positive/s^3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_of_fourthPowerError _ 0
  simp only [sub_zero]
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr hn.ne'
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_
    (sourceCubicCombinedError_tail_tendsto n hn n.natAbs hN positive)
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,self_mem_nhdsWithin]
    with s hs hspos
  have hsum := (sourceCubicCombinedError_summable_bound n hn s n.natAbs hN positive hs.1).1
  have hb := hsum.le_tsum n (fun m _ => by unfold cubicFourthPowerTail; split_ifs <;> positivity)
  have hd := div_le_div_of_nonneg_right hb (pow_nonneg hspos.le 12)
  simpa only [cubicFourthPowerTail,le_refl,if_true,div_pow,← pow_mul] using hd

/-- The moving remainder differs from its exact background by a vanishing normalized error. -/
theorem sourceCubicMovingRemainderError_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool)
    (z : ℝ → ℂ) (hz : ∀ᶠ s in 𝓝[>] (0 : ℝ), z s ∈ resonantStrip n) :
    Tendsto (fun s : ℝ =>
      (sourceCubicRemainderFunction n s n positive (z s)-(s : ℂ)^3/(z s)^2)/(s : ℂ)^3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (sourceCubicCombinedError_normalized_tendsto n hn positive)
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin,hz]
    with s hsmall hs1 hs hz
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le 3)
  simpa only [sourceCubicBackgroundFunction,if_true] using
    sourceCubicCombinedError_pointwise n n hn (le_abs_self n) s hs.le hs1.le hsmall.1 positive (z s) hz

/-- At a moving spectral parameter tending to the free center, the normalized remainder tends to its exact scale. -/
theorem sourceCubicMovingRemainder_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool)
    (z : ℝ → ℂ) (hz : ∀ᶠ s in 𝓝[>] (0 : ℝ), z s ∈ resonantStrip n)
    (ht : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ)*n))) :
    Tendsto (fun s : ℝ => sourceCubicRemainderFunction n s n positive (z s)/(s : ℂ)^3)
      (𝓝[>] (0 : ℝ)) (𝓝 (sourceCubicTailScale n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hinv : Tendsto (fun s : ℝ => (1 : ℂ)/(z s)^2) (𝓝[>] (0 : ℝ)) (𝓝 (1/((Real.pi : ℂ)*n)^2)) :=
    tendsto_const_nhds.div (ht.pow 2) (pow_ne_zero 2 (mul_ne_zero hp0 hn0))
  have h := (sourceCubicMovingRemainderError_tendsto n hn positive z hz).add
    (hinv : Tendsto (fun s : ℝ => (1 : ℂ)/(z s)^2) (𝓝[>] (0 : ℝ)) (𝓝 (1/((Real.pi : ℂ)*n)^2)))
  have he : (1 : ℂ)/((Real.pi : ℂ)*n)^2 = (sourceCubicTailScale n : ℂ) := by
    simp [sourceCubicTailScale]
  simp only [zero_add,he] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  field_simp
  ring

/-- Select either original off-diagonal coefficient of the three-mode family. -/
def sourceCubicCoefficient (n : ℤ) (s : ℝ) (positive : Bool) (z : ℂ) : ℂ :=
  if positive then sourceResonantBPlusFunction (by simp) (sourceCubicTailFamily n s) n z
  else sourceResonantBMinusFunction (by simp) (sourceCubicTailFamily n s) n z

/-- The original coefficient splits into its actual remainder and resonant leading Fourier term. -/
theorem sourceCubicCoefficient_split (n : ℤ) (hn : 0 < n) (s : ℝ) (positive : Bool) (z : ℂ) :
    sourceCubicCoefficient n s positive z = sourceCubicRemainderFunction n s n positive z+
      ((s^3*sourceCubicTailScale n : ℝ) : ℂ) := by
  have hl := sourceCubicLeadingCoefficient_tail_value n n hn (le_abs_self n) s positive
  simp only [if_true] at hl
  have he : sourceCubicCoefficient n s positive z = sourceCubicRemainderFunction n s n positive z+
      sourceCubicLeadingCoefficient n s n positive := by
    cases positive
    · have hf := unitWeightedPairEquiv_fst (sourceCubicTailFamily n s) (-(2*n))
      rw [unitWeightedPairEquiv_sourceCubicTailFamily] at hf
      simp only [sourceCubicCoefficient,sourceCubicRemainderFunction,sourceCubicLeadingCoefficient,
        Bool.false_eq_true,if_false,sourceResonantBMinusFunction,sourceCorrectionEntryFunction,
        weightedResonantBMinusExtension,unitWeightedPairEquiv_sourceCubicTailFamily,hf,sub_add_cancel]
    · have hf := unitWeightedPairEquiv_snd (sourceCubicTailFamily n s) (2*n)
      rw [unitWeightedPairEquiv_sourceCubicTailFamily] at hf
      simp only [sourceCubicCoefficient,sourceCubicRemainderFunction,sourceCubicLeadingCoefficient,
        if_true,sourceResonantBPlusFunction,sourceCorrectionEntryFunction,
        weightedResonantBPlusExtension,unitWeightedPairEquiv_sourceCubicTailFamily,hf,sub_add_cancel]
  rwa [hl] at he

/-- Both actual coefficients divided by the cubic amplitude tend to twice the resonant scale. -/
theorem sourceCubicMovingCoefficient_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool)
    (z : ℝ → ℂ) (hz : ∀ᶠ s in 𝓝[>] (0 : ℝ), z s ∈ resonantStrip n)
    (ht : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ)*n))) :
    Tendsto (fun s : ℝ => sourceCubicCoefficient n s positive (z s)/(s : ℂ)^3)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*(sourceCubicTailScale n : ℂ))) := by
  have h := (sourceCubicMovingRemainder_tendsto n hn positive z hz ht).add_const (sourceCubicTailScale n : ℂ)
  rw [← two_mul] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [sourceCubicCoefficient_split n hn s positive,add_div,Complex.ofReal_mul,Complex.ofReal_pow,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 (by exact_mod_cast (ne_of_gt hs)))]

end NLS.ZakharovShabat
