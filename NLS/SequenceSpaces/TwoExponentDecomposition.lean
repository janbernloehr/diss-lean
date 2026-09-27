import NLS.SequenceSpaces.TwoExponentMajorant

/-!
# Exact decomposition from two sequence majorants

A scalar sequence bounded coordinatewise by the sum of an `ℓq`
majorant and an `ℓr` majorant splits exactly into one sequence in each
space. Each summand has norm at most its corresponding majorant, even
when `r < 1`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {r q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Split a complex number within prescribed nonnegative norm
budgets whose sum bounds its norm. -/
private theorem exists_bounded_add_decomposition
    (z : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : ‖z‖ ≤ a+b) :
    ∃ u v : ℂ, u+v=z ∧ ‖u‖ ≤ a ∧ ‖v‖ ≤ b := by
  let d := a+b
  by_cases hd : d = 0
  · have ha0 : a = 0 := by dsimp [d] at hd; linarith
    have hb0 : b = 0 := by dsimp [d] at hd; linarith
    have hz0 : z = 0 := norm_eq_zero.mp (by
      have : ‖z‖ ≤ 0 := by simpa [ha0,hb0] using hz
      exact le_antisymm this (norm_nonneg _))
    subst z
    subst a
    subst b
    exact ⟨0,0,by simp,by simp,by simp⟩
  · have hdpos : 0 < d := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hd)
    let u : ℂ := ((a/d : ℝ) : ℂ) * z
    let v : ℂ := ((b/d : ℝ) : ℂ) * z
    have hsum : a/d+b/d = 1 := by
      rw [← add_div]
      exact div_self hd
    have huv : u+v=z := by
      calc
        u+v = ((a/d+b/d : ℝ) : ℂ) * z := by
          dsimp [u,v]
          push_cast
          ring
        _ = z := by rw [hsum]; simp
    have hunorm : ‖u‖ = (a/d)*‖z‖ := by
      simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ha hdpos.le)]
    have hvnorm : ‖v‖ = (b/d)*‖z‖ := by
      simp only [v,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hb hdpos.le)]
    refine ⟨u,v,huv,?_,?_⟩
    · rw [hunorm]
      calc
        (a/d)*‖z‖ ≤ (a/d)*d :=
          mul_le_mul_of_nonneg_left hz (div_nonneg ha hdpos.le)
        _ = a := div_mul_cancel₀ a hd
    · rw [hvnorm]
      calc
        (b/d)*‖z‖ ≤ (b/d)*d :=
          mul_le_mul_of_nonneg_left hz (div_nonneg hb hdpos.le)
        _ = b := div_mul_cancel₀ b hd

/-- Pointwise `ℓq + ℓr` majorants yield an exact `ℓq + ℓr`
decomposition with separate norm bounds. -/
theorem exists_coeff_decomposition_of_twoSequenceMajorants
    (hr : 0 < r) (a : ℤ → ℂ) (A : Coeff q) (B : Coeff r)
    (hpoint : ∀ n : ℤ, ‖a n‖ ≤ ‖A n‖+‖B n‖) :
    ∃ X : Coeff q, ∃ Y : Coeff r,
      (∀ n : ℤ, X n+Y n=a n) ∧
      ‖X‖ ≤ ‖A‖ ∧ ‖Y‖ ≤ ‖B‖ := by
  classical
  let hsplit (n : ℤ) := exists_bounded_add_decomposition
    (a n) ‖A n‖ ‖B n‖ (norm_nonneg _) (norm_nonneg _) (hpoint n)
  let u : ℤ → ℂ := fun n => Classical.choose (hsplit n)
  let v : ℤ → ℂ := fun n =>
    Classical.choose (Classical.choose_spec (hsplit n))
  have hdata (n : ℤ) :
      u n+v n=a n ∧ ‖u n‖ ≤ ‖A n‖ ∧ ‖v n‖ ≤ ‖B n‖ :=
    Classical.choose_spec (Classical.choose_spec (hsplit n))
  have humem : Memℓp u q :=
    (lp.memℓp A).mono' (fun n => (hdata n).2.1)
  have hvmem : Memℓp v r :=
    (lp.memℓp B).mono' (fun n => (hdata n).2.2)
  let X : Coeff q := ⟨u,humem⟩
  let Y : Coeff r := ⟨v,hvmem⟩
  refine ⟨X,Y,(fun n => (hdata n).1),?_,?_⟩
  · exact lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
      (fun n => (hdata n).2.1)
  · exact lp.norm_mono hr.ne' (fun n => (hdata n).2.2)

/-- Tail majorants suffice for an exact decomposition when the full
sequence is already known to lie in `ℓq`. The finitely many central
coordinates are absorbed by the `ℓq` summand with at most the norm of
the full sequence as extra cost. -/
theorem exists_coeff_decomposition_of_tailMajorants
    (hr : 0 < r) (a : Coeff q) (K : ℕ) (A : Coeff q) (B : Coeff r)
    (hpoint : ∀ n : ℤ, K ≤ n.natAbs →
      ‖a n‖ ≤ ‖A n‖+‖B n‖) :
    ∃ X : Coeff q, ∃ Y : Coeff r,
      (∀ n : ℤ, X n+Y n=a n) ∧
      ‖X‖ ≤ ‖A‖+‖a‖ ∧ ‖Y‖ ≤ ‖B‖ := by
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let C : Coeff q := magnitude A + magnitude (truncate s a)
  have hCpoint (n : ℤ) :
      ‖C n‖ = ‖A n‖+‖truncate s a n‖ := by
    simp only [C,lp.coeFn_add,Pi.add_apply,magnitude_apply]
    rw [← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hglobal (n : ℤ) : ‖a n‖ ≤ ‖C n‖+‖B n‖ := by
    by_cases hn : K ≤ n.natAbs
    · rw [hCpoint]
      have hp := hpoint n hn
      nlinarith [norm_nonneg (truncate s a n)]
    · have hns : n ∈ s := by
        simp only [s,Finset.mem_Icc]
        omega
      rw [hCpoint,truncate_apply,if_pos hns]
      nlinarith [norm_nonneg (A n),norm_nonneg (B n)]
  obtain ⟨X,Y,hXY,hX,hY⟩ :=
    exists_coeff_decomposition_of_twoSequenceMajorants hr a C B hglobal
  have htrunc : ‖truncate s a‖ ≤ ‖a‖ :=
    norm_truncate_le (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' s a
  have hCnorm : ‖C‖ ≤ ‖A‖+‖a‖ := by
    calc
      ‖C‖ ≤ ‖magnitude A‖+‖magnitude (truncate s a)‖ := norm_add_le _ _
      _ = ‖A‖+‖truncate s a‖ := by simp
      _ ≤ ‖A‖+‖a‖ := add_le_add le_rfl htrunc
  exact ⟨X,Y,hXY,hX.trans hCnorm,hY⟩

end NLS.Coeff
