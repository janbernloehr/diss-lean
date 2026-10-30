import NLS.SequenceSpaces.FullReciprocalMatrixTail
import NLS.SequenceSpaces.ReciprocalColumnHeadTail

/-!
# Operator bounds with two reciprocal spacings

One output row majorant gives a finite-head factor 2/abs(n), its actual
lp tail, and the conjugate-exponent punctured lattice norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Both inverse spacings give a quantitative operator bound by the
output head and tail of one lp majorant and the conjugate lattice norm. -/
theorem norm_operator_le_doubleReciprocal_head_tail
    (hp : p ≠ ⊤) (n : ℤ) (hn : n ≠ 0) (K : ℕ) (hK : 2*K ≤ n.natAbs)
    (T : Coeff p →L[ℂ] Coeff p) (b : Coeff p)
    (hzero : ∀ k : ℤ, (T (lp.single p k 1)) n = 0)
    (hdiag : ∀ m : ℤ, (T (lp.single p m 1)) m = 0)
    (hentry : ∀ m k : ℤ, m ≠ n → k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤ ‖b m‖/(((n-m).natAbs:ℝ)*|((k-m:ℤ):ℝ)|)) :
    ‖T‖ ≤ ((2/(n.natAbs:ℝ))*‖b‖+
      ‖b-truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) b‖)*
        ‖puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  let f : ℤ → ℂ := fun m => if m = n then 0 else b m/((n-m).natAbs:ℂ)
  have hf (m : ℤ) : ‖f m‖ ≤ ‖b m‖ := by
    by_cases hmn : m = n
    · simp only [f,if_pos hmn,norm_zero]
      exact norm_nonneg _
    · simp only [f,if_neg hmn,norm_div,Complex.norm_natCast]
      apply div_le_self (norm_nonneg _)
      exact_mod_cast (show 1 ≤ (n-m).natAbs from Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hmn)))
  let b' : Coeff p := ⟨f,(lp.memℓp b).mono' hf⟩
  have hb0 : b' n = 0 := by simp [b',f]
  have hbn (m : ℤ) (hmn : m ≠ n) : ‖b' m‖ = ‖b m‖/((n-m).natAbs:ℝ) := by
    simp only [b',f,if_neg hmn,norm_div,Complex.norm_natCast]
  have hb' := norm_le_reciprocal_column_head_tail n hn K hK b' b hb0
    (fun m hmn => (hbn m hmn).le)
  have hT : ‖T‖ ≤ ‖b'‖*
      ‖puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
    apply norm_operator_le_of_reciprocalEntries hp T b' hdiag
    intro m k hkm
    by_cases hmn : m = n
    · subst m
      rw [hzero k,hb0,norm_zero,zero_div]
    · rw [hbn m hmn,div_div]
      exact hentry m k hmn hkm
  exact hT.trans (mul_le_mul_of_nonneg_right hb' (norm_nonneg _))

end NLS.Coeff
