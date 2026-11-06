import NLS.SequenceSpaces.Reflection

/-! # Native membership from the positive half of a norm-symmetric sequence

The zero mode is a finite correction. Reflection recovers negative modes
without imposing phase equality; conjugate-reflected physical sequences
and actual even gap sequences are both covered.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS

/-- At every Banach exponent, norm symmetry makes full signed membership
equivalent to membership of the zero-extended strictly positive half. -/
theorem memlp_iff_positive_half_of_norm_neg_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℤ → ℂ)
    (hr : ∀ n : ℤ, ‖f (-n)‖=‖f n‖) :
    Memℓp f p ↔ Memℓp (fun n : ℤ => if 0<n then f n else 0) p := by
  constructor
  · intro hf
    apply hf.mono'
    intro n
    split_ifs <;> simp [norm_nonneg]
  · intro hp
    let a : Coeff p := ⟨_,hp⟩
    let b : Coeff p := a+Coeff.reflection a+lp.single p 0 (f 0)
    apply (lp.memℓp b).mono'
    intro n
    have he : ‖f n‖=‖b n‖ := by
      simp only [b,lp.coeFn_add,Pi.add_apply,Coeff.reflection_apply,lp.single_apply,Pi.single_apply]
      change ‖f n‖=‖(if 0<n then f n else 0)+(if 0< -n then f (-n) else 0)+
        (if n=0 then f 0 else 0)‖
      by_cases hn : 0<n
      · rw [if_pos hn,if_neg (by omega : ¬0< -n),if_neg (by omega : n≠(0 : ℤ))]
        simp only [add_zero]
      · by_cases h0 : n=0
        · subst n
          norm_num
        · rw [if_neg hn,if_pos (by omega : 0< -n),if_neg h0]
          simpa only [zero_add,add_zero] using (hr n).symm
    exact he.le

end NLS
