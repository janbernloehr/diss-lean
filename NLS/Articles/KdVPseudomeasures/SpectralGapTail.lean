import NLS.Articles.KdVPseudomeasures.SpectralPairs

/-!
# Endpoint regularity of the actual high-gap tail

The sequence contains the actual widths of the ordered physical high pairs,
extended evenly to signed indices, with zero at all indices below the cutoff.
Its norm is the genuine infinity-exponent Sobolev coefficient norm. This
verifies the high-tail direct regularity estimate; the low-mode count needed
to identify these mode-number slots with global canonical gaps is still open.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Raw even high-gap coefficients, zero below the explicit cutoff. -/
def sourceHighGapTailValues (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n) (k : ℤ) : ℂ :=
  if hn : N ≤ k.natAbs then ((P k.natAbs hn).right-(P k.natAbs hn).left:ℝ) else 0

/-- The signed high-gap extension is even. -/
theorem sourceHighGapTailValues_neg (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n) (k : ℤ) :
    sourceHighGapTailValues r hr q N P (-k) = sourceHighGapTailValues r hr q N P k := by
  exact congrArg (fun n : ℕ => if hn : N ≤ n then
    (((P n hn).right-(P n hn).left:ℝ):ℂ) else 0) (Int.natAbs_neg k)

/-- All raw high-gap coefficients are real. -/
theorem sourceHighGapTailValues_im (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n) (k : ℤ) :
    (sourceHighGapTailValues r hr q N P k).im = 0 := by
  unfold sourceHighGapTailValues
  split_ifs <;> rfl

/-- Weighted actual high gaps obey the exact original endpoint norm bound. -/
theorem norm_sourceHighGapTailValues_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 1 ≤ N) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n)
    (hs : ∀ (n : ℕ), N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (k : ℤ) :
    ‖(Weight.sobolev (-r) k:ℂ)*sourceHighGapTailValues r hr q N P k‖ ≤ 6*Real.sqrt 6*‖q.val‖ := by
  unfold sourceHighGapTailValues
  split_ifs with hk
  · have hgap := EndpointHillRealPair.weighted_gap_le r hr.1 hr.2 k.natAbs (hN.trans hk)
      (sourceEndpointCoefficients r q.val)
      (by simpa only [norm_sourceEndpointCoefficients] using hs k.natAbs hk) (P k.natAbs hk)
    have hW : Weight.sobolev (-r) k = Weight.sobolev (-r) (k.natAbs:ℤ) := by
      simp only [Weight.sobolev_apply]
      rw [Int.cast_natCast]
      rw [Nat.cast_natAbs, Int.cast_abs, abs_abs]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-r)).positive k), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (P k.natAbs hk).ordered), hW]
    simpa only [EndpointHillRealPair.gap, norm_sourceEndpointCoefficients] using hgap
  · simp only [mul_zero, norm_zero]
    positivity

/-- The actual evenly extended high-gap tail in the source infinity Sobolev space. -/
def sourceHighGapTail (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 1 ≤ N) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n)
    (hs : ∀ (n : ℕ), N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    WeightedCoeff (Weight.sobolev (-r)) ⊤ :=
  ⟨sourceHighGapTailValues r hr q N P, memℓp_infty ⟨6*Real.sqrt 6*‖q.val‖, by
    rintro _ ⟨k, rfl⟩
    exact norm_sourceHighGapTailValues_le r hr q N hN P hs k⟩⟩

/-- No high-gap coefficient is changed by passage to the weighted sequence space. -/
theorem sourceHighGapTail_apply (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 1 ≤ N) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n)
    (hs : ∀ (n : ℕ), N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) (k : ℤ) :
    (sourceHighGapTail r hr q N hN P hs).val k = sourceHighGapTailValues r hr q N P k := rfl

/-- The true infinity-exponent weighted high-gap norm is bounded in the original source norm. -/
theorem norm_sourceHighGapTail_le (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 1 ≤ N) (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n)
    (hs : ∀ (n : ℕ), N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    ‖sourceHighGapTail r hr q N hN P hs‖ ≤ 6*Real.sqrt 6*‖q.val‖ := by
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) ⊤ _‖ ≤ _
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  exact norm_sourceHighGapTailValues_le r hr q N hN P hs k

/-- A uniform original norm-ball cutoff gives an actual ordered physical high
tail whose gap sequence lies in the original infinity-exponent Sobolev scale. -/
theorem source_uniform_ordered_real_tail_with_gap_space (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∃ P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n,
        (∀ (n m : ℕ) (hn : N ≤ n) (hm : N ≤ m), n < m → (P n hn).right < (P m hm).left) ∧
        ∃ g : WeightedCoeff (Weight.sobolev (-r)) ⊤,
          (∀ k : ℤ, g.val k = sourceHighGapTailValues r hr q N P k) ∧ ‖g‖ ≤ 6*Real.sqrt 6*‖q.val‖ := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 R
  refine ⟨N, hN, ?_⟩
  intro q hq
  have hs (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)
  let P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n :=
    fun n hn => sourceHillRealPair r hr n (hN.trans hn) q (hs n hn)
  refine ⟨P, ?_, sourceHighGapTail r hr q N hN P hs,
    sourceHighGapTail_apply r hr q N hN P hs, norm_sourceHighGapTail_le r hr q N hN P hs⟩
  intro n m hn hm hnm
  exact SourceHillRealPair.right_lt_left r hr q n (hN.trans hn) m hnm (P n hn) (P m hm)

end NLS.Articles.KdVPseudomeasures
