import NLS.SequenceSpaces.PositiveSquaredGapMomentBound

/-! The inverse-row-index weight reduces the actual two signed
reciprocal factors to one convolution kernel and an inverse-row tail. -/
noncomputable section
open Set
namespace NLS.Coeff

theorem positive_weighted_moment_kernel_le (n m : ℕ+) (hmn : m ≠ n) :
    (((m:ℕ):ℝ)/(n:ℕ))*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) ≤
      1/|((n:ℕ):ℝ)-(m:ℕ)|+2/((n:ℕ):ℝ) := by
  let x := ((n:ℕ):ℝ)
  let y := ((m:ℕ):ℝ)
  let d := |x-y|
  have hx : 0 < x := by dsimp [x]; exact_mod_cast n.pos
  have hy : 0 < y := by dsimp [y]; exact_mod_cast m.pos
  have hne : x ≠ y := by
    intro h
    dsimp only [x,y] at h
    have he : (n:ℕ)=(m:ℕ) := by exact_mod_cast h
    exact hmn (PNat.coe_injective he.symm)
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hxy : y ≤ x+d := by
    have h := le_abs_self (y-x)
    rw [abs_sub_comm y x] at h
    dsimp only [d]
    linarith
  have h₁ : y/(x*d) ≤ 1/d+1/x := by
    rw [div_le_iff₀ (mul_pos hx hd)]
    have he : (1/d+1/x)*(x*d)=x+d := by field_simp
    rw [he]
    exact hxy
  have h₂ : y/(x*(x+y)) ≤ 1/x := by
    rw [div_le_iff₀ (mul_pos hx (add_pos hx hy))]
    have he : 1/x*(x*(x+y))=x+y := by field_simp
    rw [he]
    linarith
  change (y/x)*(1/d+1/(x+y)) ≤ 1/d+2/x
  calc
    _ = y/(x*d)+y/(x*(x+y)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ ≤ (1/d+1/x)+1/x := add_le_add h₁ h₂
    _ = _ := by ring

end NLS.Coeff
