import NLS.Poisson.GardnerBivector

/-! Unit-period Gardner pairing for arbitrary cotangents whose nonzero
Fourier modes are prescribed. Constant modes are automatically annihilated. -/
noncomputable section
open Complex
namespace NLS.Poisson

theorem gardnerBivector_of_nonzero_modes (a b : WeightedCoeff (Weight.sobolev 1) 2)
    (n m : ℤ) (hn : n ≠ 0) (c d : ℂ)
    (ha : ∀ k : ℤ, k ≠ 0 → a.val k=if k= -n then c else 0)
    (hb : ∀ k : ℤ, k ≠ 0 → b.val k=if k= -m then d else 0) :
    gardnerBivector a b=if m= -n then (2*Real.pi:ℂ)*I*n*c*d else 0 := by
  rw [gardnerBivector_eq_tsum,tsum_eq_single (-n)]
  · rw [ha (-n) (neg_ne_zero.mpr hn),if_pos rfl,neg_neg,hb n hn]
    by_cases hmn : m= -n
    · rw [if_pos hmn,if_pos (by omega : n= -m)]
      simp only [Int.cast_neg]
      ring
    · rw [if_neg hmn,if_neg (by omega : n ≠ -m),mul_zero,mul_zero]
  · intro k hk
    by_cases hk0 : k=0
    · subst k
      simp only [Int.cast_zero,neg_zero,mul_zero,zero_mul]
    · rw [ha k hk0,if_neg hk,zero_mul]

end NLS.Poisson
