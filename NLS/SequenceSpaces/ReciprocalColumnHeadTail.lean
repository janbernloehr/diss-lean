import NLS.SequenceSpaces.FullReciprocalMatrixTail

/-!
# Explicit reciprocal head and tail bounds

A reciprocal column is controlled by a finite head with factor 2/abs(n)
and the actual lp tail of its row majorant. A single-coordinate version
makes the same bound uniform over the output index. Both results use
signed integer indices and every Banach coefficient exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A reciprocal column is bounded by its distant head and the actual lp
tail of its row majorant. The constants are 2 on the head and 1 on the tail. -/
theorem norm_le_reciprocal_column_head_tail
    (n : ℤ) (hn : n ≠ 0) (K : ℕ) (hK : 2*K ≤ n.natAbs)
    (x b : Coeff p) (hzero : x n = 0)
    (hentry : ∀ m : ℤ, m ≠ n → ‖x m‖ ≤ ‖b m‖/((n-m).natAbs:ℝ)) :
    ‖x‖ ≤ (2/(n.natAbs:ℝ))*‖b‖ +
      ‖b-truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) b‖ := by
  classical
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let A : ℝ := 2/(n.natAbs:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn0 : 0 < (n.natAbs:ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr hn
  have hhead (m : ℤ) : ‖truncate s x m‖ ≤ ‖((A:ℂ) • b) m‖ := by
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hA]
    by_cases hm : m ∈ s
    · rw [truncate_apply,if_pos hm]
      by_cases hmn : m = n
      · subst m
        rw [hzero,norm_zero]
        positivity
      · have hmK : m.natAbs ≤ K := by
          simp only [s,Finset.mem_Icc] at hm
          omega
        have htri : n.natAbs ≤ (n-m).natAbs+m.natAbs := by
          simpa only [sub_add_cancel] using Int.natAbs_add_le (n-m) m
        have hd0 : 0 < ((n-m).natAbs:ℝ) := by
          exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hmn))
        have hd : (n.natAbs:ℝ) ≤ 2*((n-m).natAbs:ℝ) := by
          exact_mod_cast (show n.natAbs ≤ 2*(n-m).natAbs by omega)
        apply (hentry m hmn).trans
        apply (div_le_iff₀ hd0).mpr
        dsimp only [A]
        calc
          ‖b m‖ ≤ (2*((n-m).natAbs:ℝ)/(n.natAbs:ℝ))*‖b m‖ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              ((one_le_div hn0).mpr hd) (norm_nonneg (b m))
          _ = _ := by ring
    · rw [truncate_apply,if_neg hm,norm_zero]
      positivity
  have hheadNorm : ‖truncate s x‖ ≤ A*‖b‖ := by
    calc
      ‖truncate s x‖ ≤ ‖(A:ℂ) • b‖ :=
        lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hhead
      _ = A*‖b‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA]
  have htail (m : ℤ) : ‖(x-truncate s x) m‖ ≤ ‖(b-truncate s b) m‖ := by
    by_cases hm : m ∈ s
    · simp [truncate_apply,hm]
    · simp only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hm,sub_zero]
      by_cases hmn : m = n
      · subst m
        rw [hzero,norm_zero]
        positivity
      · have hd : (1:ℝ) ≤ ((n-m).natAbs:ℝ) := by
          exact_mod_cast (show 1 ≤ (n-m).natAbs from
            Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hmn)))
        exact (hentry m hmn).trans (div_le_self (norm_nonneg _) hd)
  have htailNorm : ‖x-truncate s x‖ ≤ ‖b-truncate s b‖ :=
    lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' htail
  calc
    ‖x‖ = ‖truncate s x+(x-truncate s x)‖ := by congr 1; abel
    _ ≤ ‖truncate s x‖+‖x-truncate s x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hheadNorm htailNorm

/-- The same head/tail bound controls every single reciprocal entry,
uniformly over the output index. -/
theorem reciprocalEntry_le_head_tail
    (n : ℤ) (hn : n ≠ 0) (K : ℕ) (hK : 2*K ≤ n.natAbs)
    (b : Coeff p) (m : ℤ) (hmn : m ≠ n) :
    ‖b m‖/((n-m).natAbs:ℝ) ≤ (2/(n.natAbs:ℝ))*‖b‖+
      ‖b-truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) b‖ := by
  let x : Coeff p := lp.single p m (b m/((n-m).natAbs:ℂ))
  have hx : x n = 0 := by simp [x,lp.single_apply,Ne.symm hmn]
  have hb (k : ℤ) (hkn : k ≠ n) : ‖x k‖ ≤ ‖b k‖/((n-k).natAbs:ℝ) := by
    by_cases hkm : k = m
    · subst k
      simp [x]
    · simp only [x,lp.single_apply_ne _ _ _ hkm,norm_zero]
      positivity
  simpa only [x,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)),norm_div,
    Complex.norm_natCast] using norm_le_reciprocal_column_head_tail n hn K hK x b hx hb

end NLS.Coeff
