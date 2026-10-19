import NLS.SequenceSpaces.WeightedMultiplier

/-! # A decaying factor on a leading Sobolev term

An inverse-index multiplier raises the regularity of a leading term with a known smoother remainder.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- Multiplying a leading Fourier approximation by an inverse-index
symbol gives a one-order smoother tail, including every larger cutoff. -/
theorem exists_sobolev_decaying_leading_tail
    (s K₀ K : ℕ) (hK : K₀ ≤ K)
    (a : WeightedCoeff (Weight.sobolev (s:ℝ)) 2)
    (e : WeightedCoeff (Weight.sobolev ((s+1:ℕ):ℝ)) 2)
    (L phase factor : ℤ → ℂ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (he : ∀ n, e.val n = if K₀ ≤ n.natAbs then L n-phase n*a.val n else 0)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hfactor : ∀ n, K ≤ n.natAbs → ‖factor n‖ ≤ B)
    (hdecay : ∀ n : ℤ, K ≤ n.natAbs → (1+|(n:ℝ)|)*‖factor n‖ ≤ C) :
    ∃ q : WeightedCoeff (Weight.sobolev ((s+1:ℕ):ℝ)) 2,
      (∀ n, q.val n = if K ≤ n.natAbs then factor n*L n else 0) ∧
      ‖q‖ ≤ B*‖e‖+C*‖a‖ := by
  classical
  let w := Weight.sobolev (s:ℝ)
  let v := Weight.sobolev ((s+1:ℕ):ℝ)
  let m (n : ℤ) : ℂ := if K ≤ n.natAbs then factor n else 0
  let d (n : ℤ) : ℂ := if K ≤ n.natAbs then factor n*phase n else 0
  have hm (n : ℤ) : v n*‖m n‖ ≤ B*v n := by
    by_cases hn : K ≤ n.natAbs
    · simp only [m,if_pos hn]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfactor n hn) (v.positive n).le
    · simp only [m,if_neg hn,norm_zero,mul_zero]
      exact mul_nonneg hB (v.positive n).le
  have hd (n : ℤ) : (1+|(n:ℝ)|)*‖d n‖ ≤ C := by
    by_cases hn : K ≤ n.natAbs
    · simp only [d,if_pos hn,norm_mul]
      calc
        _ ≤ (1+|(n:ℝ)|)*(‖factor n‖*1) := by gcongr; exact hphase n
        _ ≤ C := by simpa only [mul_one] using hdecay n hn
    · simpa only [d,if_neg hn,norm_zero,mul_zero] using hC
  have hdw (n : ℤ) : v n*‖d n‖ ≤ C*w n := by
    simp only [v,w,Weight.sobolev_apply,Real.rpow_natCast,pow_succ]
    calc
      _ = (1+|(n:ℝ)|)^s*((1+|(n:ℝ)|)*‖d n‖) := by ring
      _ ≤ (1+|(n:ℝ)|)^s*C := mul_le_mul_of_nonneg_left (hd n) (by positivity)
      _ = _ := by ring
  let q₀ := weightedMultiplier v v m B hm e
  let q₁ := weightedMultiplier w v d C hdw a
  refine ⟨q₀+q₁,?_,?_⟩
  · intro n
    change m n*e.val n+d n*a.val n = _
    rw [he n]
    by_cases hn : K ≤ n.natAbs
    · simp only [m,d,if_pos hn,if_pos (hK.trans hn)]
      ring
    · simp [m,d,hn]
  · exact (norm_add_le _ _).trans (add_le_add
      (norm_weightedMultiplier_le v v m B hB hm e)
      (norm_weightedMultiplier_le w v d C hC hdw a))

end NLS.WeightedCoeff
