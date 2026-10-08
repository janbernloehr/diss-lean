import NLS.SequenceSpaces.LinearWeightLattice

/-! # The bilateral reciprocal-square tail in Proposition 25.5 -/
noncomputable section
namespace NLS.ReciprocalSeries

/-- The inclusive bracket-square tail is summable, including cutoff zero. -/
theorem summable_bracketSquareTail (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then bracketInverseSq n else 0) := by
  apply summable_bracketInverseSq.of_nonneg_of_le
  · intro n; split_ifs <;> first | exact bracketInverseSq_nonneg n | positivity
  · intro n; split_ifs <;> first | exact le_rfl | exact bracketInverseSq_nonneg n

/-- The source estimate ∑_{|n|≥N} ⟨n⟩⁻² ≤ 3/⟨N⟩ retains its boundary and zero mode. -/
theorem tsum_bracketSquareTail_le (N : ℕ) :
    (∑' n : ℤ, if N ≤ n.natAbs then bracketInverseSq n else 0) ≤ 3/(1+(N:ℝ)) := by
  cases N with
  | zero =>
    simp only [Nat.zero_le,ite_true,Nat.cast_zero,add_zero,div_one]
    exact tsum_bracketInverseSq_le.trans (by norm_num)
  | succ K =>
    let f : ℤ → ℝ := fun n => if K+1 ≤ n.natAbs then bracketInverseSq n else 0
    have hs : Summable f := summable_bracketSquareTail (K+1)
    have hp := hs.comp_injective (i := fun n : ℕ => (n:ℤ)+1) (by intro a b h; dsimp only at h; omega)
    have hm := hs.comp_injective (i := fun n : ℕ => -((n:ℤ)+1)) (by intro a b h; dsimp only at h; omega)
    have he (j : ℕ) : f (-((j:ℤ)+1)) = f ((j:ℤ)+1) := by
      simp only [f,Int.natAbs_neg,bracketInverseSq,Int.cast_neg,abs_neg]
    have hshift : (∑' j : ℕ, f ((j:ℤ)+1)) =
        ∑' j : ℕ, ((j:ℝ)+(K:ℝ)+2)^(-(2:ℝ)) := by
      have h := hp.sum_add_tsum_nat_add K
      simp only [Function.comp_apply] at h
      have hzero : (∑ j ∈ Finset.range K, f ((j:ℤ)+1)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjK := Finset.mem_range.mp hj
        simp only [f,show ¬K+1 ≤ ((j:ℤ)+1).natAbs by omega,ite_false]
      rw [hzero,zero_add] at h
      rw [← h]
      apply tsum_congr
      intro j
      have hj : K+1 ≤ (((j+K:ℕ):ℤ)+1).natAbs := by omega
      change (if K+1 ≤ (((j+K:ℕ):ℤ)+1).natAbs then bracketInverseSq (((j+K:ℕ):ℤ)+1) else 0) = _
      rw [if_pos hj]
      simp only [bracketInverseSq,Nat.cast_add,Int.cast_add,
        Int.cast_natCast,Int.cast_one,abs_of_nonneg (by positivity : 0 ≤ (j:ℝ)+K+1)]
      rw [Real.rpow_neg (by positivity : 0 ≤ (j:ℝ)+K+2),Real.rpow_two,one_div]
      congr 2
      ring
    have hall : (∑' n : ℤ, f n) = 2*∑' j : ℕ, ((j:ℝ)+(K:ℝ)+2)^(-(2:ℝ)) := by
      rw [tsum_of_add_one_of_neg_add_one hp hm]
      simp only [he,hshift,f,Int.natAbs_zero,show ¬K+1 ≤ 0 by omega,ite_false,add_zero]
      ring
    change (∑' n : ℤ, f n) ≤ _
    rw [hall]
    have hb := tsum_nat_shifted_rpow_le (β := (K:ℝ)+2) (by positivity) (q := 2) (by norm_num)
    simp only [show (1:ℝ)-2 = -1 by norm_num,show (2:ℝ)-1 = 1 by norm_num,
      div_one,Real.rpow_neg (by positivity : 0 ≤ (K:ℝ)+2),Real.rpow_two] at hb
    have hb' : (∑' j : ℕ, ((j:ℝ)+(K:ℝ)+2)^(-(2:ℝ))) ≤
        ((K:ℝ)+2)⁻¹^2+((K:ℝ)+2)⁻¹ := by
      simpa only [add_assoc,inv_pow,pow_one,Real.rpow_one] using hb
    have hi : ((K:ℝ)+2)⁻¹ ≤ 1/2 := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 2)
        (show (2:ℝ) ≤ (K:ℝ)+2 by linarith [Nat.cast_nonneg (α := ℝ) K])
    rw [Nat.cast_add,Nat.cast_one,show (1:ℝ)+((K:ℝ)+1) = (K:ℝ)+2 by ring,div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr (by positivity : 0 ≤ (K:ℝ)+2)]

end NLS.ReciprocalSeries
