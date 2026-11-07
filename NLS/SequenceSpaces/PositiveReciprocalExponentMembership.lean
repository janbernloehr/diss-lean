import NLS.SequenceSpaces.PositiveReciprocalMembership

/-! # Exact positive-half membership under an invertible bounded symbol -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

theorem memlp_positive_product_iff_exponent
    {p : ℝ≥0∞} [Fact (1≤p)] (a b : Coeff ⊤)
    (hab : ∀ j : ℤ, 0 < j → a j*b j = 1) (f : ℤ → ℂ) :
    Memℓp (fun j : ℤ => if 0 < j then a j*f j else 0) p ↔
      Memℓp (fun j : ℤ => if 0 < j then f j else 0) p := by
  constructor
  · intro h
    let x : Coeff p := ⟨_,h⟩
    have he : (fun j : ℤ => if 0 < j then f j else 0) = fun j => holderProduct (q := p) b x j := by
      funext j
      change (if 0 < j then f j else 0) = b j*(if 0 < j then a j*f j else 0)
      by_cases hj : 0 < j
      · rw [if_pos hj,if_pos hj]
        calc
          f j = (a j*b j)*f j := by rw [hab j hj,one_mul]
          _ = _ := by ring
      · rw [if_neg hj,if_neg hj,mul_zero]
    rw [he]
    exact lp.memℓp _
  · intro h
    let x : Coeff p := ⟨_,h⟩
    have he : (fun j : ℤ => if 0 < j then a j*f j else 0) = fun j => holderProduct (q := p) a x j := by
      funext j
      change (if 0 < j then a j*f j else 0) = a j*(if 0 < j then f j else 0)
      by_cases hj : 0 < j <;> simp only [hj,↓reduceIte,mul_zero]
    rw [he]
    exact lp.memℓp _

end NLS.Coeff
