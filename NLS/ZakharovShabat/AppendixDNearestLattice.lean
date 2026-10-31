import NLS.ZakharovShabat.AppendixDExteriorGeometry
import Mathlib.Algebra.Order.Round

/-! # Selecting the real lattice index in the proof of D.5 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Every exterior point admits the nearest real lattice index and the factor-four bound. -/
theorem exists_appendixDExterior_nearest_lattice {z : ℂ} (hz : z ∈ appendixDExterior) :
    ∃ n : ℤ, |z.re-Real.pi*n| ≤ Real.pi/2 ∧
      Real.pi/4 ≤ ‖z-(Real.pi:ℂ)*n‖ ∧
      ∀ m : ℤ, 1+|((n-m:ℤ):ℝ)|+|z.im| ≤ 4*‖z-(Real.pi:ℂ)*m‖ := by
  let n := round (z.re/Real.pi)
  have he : z.re-Real.pi*n = Real.pi*(z.re/Real.pi-n) := by
    field_simp
  have hn : |z.re-Real.pi*n| ≤ Real.pi/2 := by
    rw [he,abs_mul,abs_of_pos Real.pi_pos]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (abs_sub_round (z.re/Real.pi)) Real.pi_pos.le
  exact ⟨n,hn,hz n,appendixDExterior_denominator_le_four hz n hn⟩

end NLS.ZakharovShabat
