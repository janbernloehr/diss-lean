import NLS.ZakharovShabat.FreeHalfDiscGeometry
import NLS.ZakharovShabat.ResonantDeterminantBounds

/-!
# Linear separation of free quarter-π discs

The distant isolating neighborhoods in Lemma 10.1 are the fixed free
quarter-π discs. Their pointwise distances grow linearly in the difference
of signed indices.
-/

namespace NLS.ZakharovShabat
open Set Metric

/-- Any points in two distinct free quarter-π discs have distance
comparable to the difference of their signed indices. -/
theorem refinedResonantDisk_pointwise_separation
    {m n : ℤ} (hmn : m ≠ n) {z w : ℂ}
    (hz : z ∈ refinedResonantDisk m) (hw : w ∈ refinedResonantDisk n) :
    (Real.pi/2)*|((m-n : ℤ) : ℝ)| ≤ dist z w ∧
      dist z w ≤ (3*Real.pi/2)*|((m-n : ℤ) : ℝ)| := by
  let k : ℝ := |((m-n : ℤ) : ℝ)|
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hz' : dist z ((Real.pi : ℂ)*m) < Real.pi/4 := by
    simpa only [refinedResonantDisk, mem_ball] using hz
  have hw' : dist w ((Real.pi : ℂ)*n) < Real.pi/4 := by
    simpa only [refinedResonantDisk, mem_ball] using hw
  have hc : dist ((Real.pi : ℂ)*m) ((Real.pi : ℂ)*n) = Real.pi*k := by
    simpa only [dist_eq_norm,k] using norm_free_center_sub m n
  have h₁ := dist_triangle4 ((Real.pi : ℂ)*m) z w ((Real.pi : ℂ)*n)
  have h₂ := dist_triangle4 z ((Real.pi : ℂ)*m) ((Real.pi : ℂ)*n) w
  rw [dist_comm ((Real.pi : ℂ)*m) z, hc] at h₁
  rw [hc,dist_comm ((Real.pi : ℂ)*n) w] at h₂
  have hgap : (Real.pi/2)*k ≤ Real.pi*k-Real.pi/2 := by
    have h := mul_nonneg (show 0 ≤ Real.pi/2 by positivity) (sub_nonneg.mpr hk)
    nlinarith
  have hupper : Real.pi*k+Real.pi/2 ≤ (3*Real.pi/2)*k := by
    have h := mul_nonneg (show 0 ≤ Real.pi/2 by positivity) (sub_nonneg.mpr hk)
    nlinarith
  constructor <;> dsimp [k] at * <;> linarith

/-- Distinct free quarter-π discs are disjoint. -/
theorem refinedResonantDisk_disjoint {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (refinedResonantDisk m) (refinedResonantDisk n) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have h := (refinedResonantDisk_pointwise_separation hmn hz hw).1
  simp only [dist_self] at h
  have hk : (1 : ℝ) ≤ |((m-n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
