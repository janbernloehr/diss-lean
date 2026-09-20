import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-!
# Half-pi free circles avoid the free lattice

The radius leaves room for Cauchy circles around the source's quarter-pi
samples while keeping every boundary point off the lattice.
-/

namespace NLS.ZakharovShabat
open Set Metric

/-- A half-pi free circle contains no free lattice point. -/
theorem freeHalfSphere_notMem_freeLattice (n : ℤ) {z : ℂ}
    (hz : z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/2)) : z ∉ freeLattice := by
  rintro ⟨k, rfl⟩
  have hd : ‖(Real.pi : ℂ)*k-(Real.pi : ℂ)*n‖ = Real.pi/2 := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  rw [norm_free_center_sub] at hd
  by_cases hkn : k = n
  · subst k
    simp only [sub_self, Int.cast_zero, abs_zero, mul_zero] at hd
    linarith [Real.pi_pos]
  · have hk : (1 : ℝ) ≤ |((k-n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn)
    have h := mul_le_mul_of_nonneg_left hk Real.pi_pos.le
    rw [mul_one] at h
    linarith [Real.pi_pos]

end NLS.ZakharovShabat
