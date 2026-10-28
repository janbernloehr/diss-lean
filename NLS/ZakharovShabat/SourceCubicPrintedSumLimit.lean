import NLS.ZakharovShabat.SourceCubicCoefficientLimit

/-! # The exact normalized right-hand side of the final p.44 sum

These statements concern original period-two coefficients, actual whole-strip
suprema and infinite signed sums. The final source inequality still requires
the asymptotics of the actual counted-root gap; it is not resolved here.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicPrintedSumLimitFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The selected original leading Fourier coefficient, with the physical minus sign retained. -/
def sourceCubicLeadingCoefficient (n : ℤ) (s : ℝ) (m : ℤ) (positive : Bool) : ℂ :=
  if positive then (sourceCubicTailFamily n s).snd (2*m)
  else (sourceCubicTailFamily n s).fst (-(2*m))

/-- Only the resonant target contributes a leading coefficient on the outer tail. -/
theorem sourceCubicLeadingCoefficient_tail_value (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s : ℝ) (positive : Bool) :
    sourceCubicLeadingCoefficient n s m positive = if m=n then ((s^3*sourceCubicTailScale n : ℝ) : ℂ) else 0 := by
  have hlow : ¬(2*m=0 ∨ 2*m=n) := by
    rcases le_abs.mp hm with hm | hm <;> omega
  have hlow' : ¬(-(2*m)=0 ∨ -(2*m)= -n) := by omega
  have hpos : 2*m=2*n ↔ m=n := by omega
  have hneg : -(2*m)= -(2*n) ↔ m=n := by omega
  cases positive
  · simp only [sourceCubicLeadingCoefficient,Bool.false_eq_true,if_false,sourceCubicTailFamily_fst n hn,
      if_neg hlow',zero_add,hneg]
  · simp only [sourceCubicLeadingCoefficient,if_true,sourceCubicTailFamily_snd n hn,if_neg hlow,zero_add,hpos]

/-- The leading fourth-power tail is exactly a single-index function. -/
theorem sourceCubicLeadingCoefficient_fourthTail (n : ℤ) (hn : 0 < n) (s : ℝ) (positive : Bool) :
    cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m positive‖) =
      fun m => if m=n then ‖((s^3*sourceCubicTailScale n : ℝ) : ℂ)‖^4 else 0 := by
  funext m
  dsimp only [cubicFourthPowerTail]
  by_cases hm : n.natAbs ≤ m.natAbs
  · rw [if_pos hm,sourceCubicLeadingCoefficient_tail_value n m hn (sourceCubicTail_abs_index n m hn hm) s positive]
    split_ifs <;> simp
  · have hmn : m ≠ n := by intro h; subst m; exact hm le_rfl
    simp [hm,hmn]

/-- The normalized leading Fourier sum is exactly the fourth power of its fixed scale. -/
theorem sourceCubicLeadingCoefficient_sum_scaled (n : ℤ) (hn : 0 < n) (s : ℝ) (hs : s ≠ 0) (positive : Bool) :
    (∑' m, cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m positive‖) m)/s^12 = (sourceCubicTailScale n)^4 := by
  rw [sourceCubicLeadingCoefficient_fourthTail n hn,tsum_ite_eq]
  simp only [Complex.norm_real,Real.norm_eq_abs,← abs_pow]
  rw [abs_of_nonneg (show 0 ≤ (s^3*sourceCubicTailScale n)^4 by positivity)]
  field_simp

/-- The leading Fourier fourth-power tail is summable. -/
theorem sourceCubicLeadingCoefficient_summable (n : ℤ) (hn : 0 < n) (s : ℝ) (positive : Bool) :
    Summable (cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m positive‖)) := by
  rw [sourceCubicLeadingCoefficient_fourthTail n hn]
  exact (hasSum_ite_eq n _).summable

/-- The normalized leading Fourier sum has its constant limit. -/
theorem sourceCubicLeadingCoefficient_sum_tendsto (n : ℤ) (hn : 0 < n) (positive : Bool) :
    Tendsto (fun s : ℝ => (∑' m, cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m positive‖) m)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 ((sourceCubicTailScale n)^4)) := by
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact sourceCubicLeadingCoefficient_sum_scaled n hn s (ne_of_gt hs) positive

/-- The four separated sums of leading coefficients and original remainder suprema. -/
def sourceCubicFourTermRightSum (n : ℤ) (s : ℝ) : ℝ :=
  (∑' m, cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m false‖) m)+
  (∑' m, cubicFourthPowerTail n.natAbs (fun m => ‖sourceCubicLeadingCoefficient n s m true‖) m)+
  (∑' m, cubicFourthPowerTail n.natAbs (fun m => sourceCubicRemainderSup n s m false) m)+
  (∑' m, cubicFourthPowerTail n.natAbs (fun m => sourceCubicRemainderSup n s m true) m)

/-- All four normalized source sums converge to their exact combined limit. -/
theorem sourceCubicFourTermRightSum_tendsto (n : ℤ) (hn : 0 < n) :
    Tendsto (fun s : ℝ => sourceCubicFourTermRightSum n s/s^12) (𝓝[>] (0 : ℝ))
      (𝓝 (2*(sourceCubicTailScale n)^4+2*(sourceCubicBackgroundScale n)^4)) := by
  have h := (((sourceCubicLeadingCoefficient_sum_tendsto n hn false).add (sourceCubicLeadingCoefficient_sum_tendsto n hn true)).add
    (sourceCubicRemainderSup_sum_normalized_tendsto n hn false)).add (sourceCubicRemainderSup_sum_normalized_tendsto n hn true)
  have he : (sourceCubicTailScale n)^4+(sourceCubicTailScale n)^4+
      (sourceCubicBackgroundScale n)^4+(sourceCubicBackgroundScale n)^4 =
      2*(sourceCubicTailScale n)^4+2*(sourceCubicBackgroundScale n)^4 := by ring
  simpa only [sourceCubicFourTermRightSum,add_div,he] using h

/-- The literal grouped right-hand side on p.44 for p=4, unit weight and cutoff abs(n). -/
def sourceCubicPrintedRightSum (n : ℤ) (s : ℝ) : ℝ :=
  (∑' m : ℤ, if n.natAbs ≤ m.natAbs then
    ‖(sourceCubicTailFamily n s).fst (-(2*m))‖^4+‖(sourceCubicTailFamily n s).snd (2*m)‖^4 else 0) +
  (∑' m : ℤ, if n.natAbs ≤ m.natAbs then
    (sourceResonantBMinusSup (by simp) SpectralWeight.one (sourceCubicTailFamily n s) m)^4+
    (sourceResonantBPlusSup (by simp) SpectralWeight.one (sourceCubicTailFamily n s) m)^4 else 0)

/-- Summability identifies the literal grouped source sum with its four separate terms. -/
theorem sourceCubicPrintedRightSum_eq (n : ℤ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : SourceCubicSmall n s) : sourceCubicPrintedRightSum n s = sourceCubicFourTermRightSum n s := by
  have hl := (sourceCubicLeadingCoefficient_summable n hn s false).tsum_add (sourceCubicLeadingCoefficient_summable n hn s true)
  have hr := (sourceCubicRemainderSup_fourth_summable n hn s false hs hs1 hsmall).tsum_add
    (sourceCubicRemainderSup_fourth_summable n hn s true hs hs1 hsmall)
  have he (u v : ℤ → ℝ) : (fun m : ℤ => if n.natAbs ≤ m.natAbs then (u m)^4+(v m)^4 else 0) =
      fun m => cubicFourthPowerTail n.natAbs u m+cubicFourthPowerTail n.natAbs v m := by
    funext m
    unfold cubicFourthPowerTail
    split_ifs <;> simp
  change (∑' m, if n.natAbs ≤ m.natAbs then ‖sourceCubicLeadingCoefficient n s m false‖^4+‖sourceCubicLeadingCoefficient n s m true‖^4 else 0)+
    (∑' m, if n.natAbs ≤ m.natAbs then (sourceCubicRemainderSup n s m false)^4+(sourceCubicRemainderSup n s m true)^4 else 0) = _
  rw [he,he,hl,hr]
  unfold sourceCubicFourTermRightSum
  ring

/-- The actual entire right-hand side divided by s^12 has its exact infinite-sum limit. -/
theorem sourceCubicPrintedRightSum_normalized_tendsto (n : ℤ) (hn : 0 < n) :
    Tendsto (fun s : ℝ => sourceCubicPrintedRightSum n s/s^12) (𝓝[>] (0 : ℝ))
      (𝓝 (2*(sourceCubicTailScale n)^4+2*(sourceCubicBackgroundScale n)^4)) := by
  apply (tendsto_congr' ?_).mpr (sourceCubicFourTermRightSum_tendsto n hn)
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin]
    with s hsmall hs1 hs
  rw [sourceCubicPrintedRightSum_eq n hn s hs hs1.le hsmall.1]

/-- For every target n>=3, the exact right-hand-side limit is below the proposed spectral comparison value. This does not prove a spectral-gap limit. -/
theorem sourceCubicPrintedRightSum_limit_lt (n : ℤ) (hn : 3 ≤ n) :
    2*(sourceCubicTailScale n)^4+2*(sourceCubicBackgroundScale n)^4 < 16*(sourceCubicTailScale n)^4 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd : (n : ℝ)-1/2 ≠ 0 := by linarith
  have hr : 0 < sourceCubicTailScale n := by
    unfold sourceCubicTailScale
    exact one_div_pos.mpr (sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero hn0))
  have he : (sourceCubicBackgroundScale n)^4 = (sourceCubicTailScale n)^4*((n : ℝ)/((n : ℝ)-1/2))^8 := by
    unfold sourceCubicBackgroundScale sourceCubicTailScale
    field_simp
  have h := mul_lt_mul_of_pos_right (resonantCubic_limit_ratio_lt n hn) (pow_pos hr 4)
  rw [he]
  nlinarith

end NLS.ZakharovShabat
