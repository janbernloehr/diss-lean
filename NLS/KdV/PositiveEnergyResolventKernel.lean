import NLS.KdV.HighEnergyDiscSeparation

/-! # Positive-index quadratic resolvent row estimates -/
noncomputable section
namespace NLS.KdV

theorem positiveIndex_abs_sub_ge_one (k m : ℕ+) (hkm : k ≠ m) :
    1 ≤ |(k : ℝ)-(m : ℝ)| := by
  have hne : (k : ℕ) ≠ (m : ℕ) := fun h => hkm (Subtype.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (k : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast h
    exact le_trans (by linarith : 1 ≤ -((k : ℝ)-(m : ℝ))) (neg_le_abs _)
  · have hh : (m : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast h
    exact le_trans (by linarith : 1 ≤ (k : ℝ)-(m : ℝ)) (le_abs_self _)

theorem positiveIndex_squared_sub_ne_zero (k m : ℕ+) (hkm : k ≠ m) :
    (k : ℝ)^2-(m : ℝ)^2 ≠ 0 := by
  have hd : (k : ℝ)-(m : ℝ) ≠ 0 := by
    intro h
    have hh := positiveIndex_abs_sub_ge_one k m hkm
    rw [h,abs_zero] at hh
    norm_num at hh
  rw [sq_sub_sq]
  exact mul_ne_zero (by positivity) hd

theorem positiveIndex_resolvent_kernel_le (k m n : ℕ+) (hkm : k ≠ m) :
    ((k : ℝ)^2+(n : ℝ)^2)/((m : ℝ)*|(k : ℝ)^2-(m : ℝ)^2|) ≤
      (1+(n : ℝ)^2)*(1/(m : ℝ)+1/|(k : ℝ)-(m : ℝ)|) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hk : (0 : ℝ) ≤ k := by positivity
  let d := |(k : ℝ)-(m : ℝ)|
  let s := (k : ℝ)+(m : ℝ)
  have hd : 1 ≤ d := positiveIndex_abs_sub_ge_one k m hkm
  have hs : 1 ≤ s := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    dsimp only [s]
    linarith
  have hkd : (k : ℝ) ≤ d+(m : ℝ) := by
    have hh := le_abs_self ((k : ℝ)-(m : ℝ))
    dsimp only [d]
    linarith
  have hks : (k : ℝ) ≤ s := by dsimp only [s]; linarith
  have hprod : 1 ≤ s*(d+(m : ℝ)) := by nlinarith
  have hK : (k : ℝ)^2 ≤ s*(d+(m : ℝ)) := by
    simpa only [pow_two] using mul_le_mul hks hkd hk (by positivity : 0 ≤ s)
  have hN := mul_le_mul_of_nonneg_left hprod (sq_nonneg (n : ℝ))
  have hnum : (k : ℝ)^2+(n : ℝ)^2 ≤ (1+(n : ℝ)^2)*s*(d+(m : ℝ)) := by nlinarith
  have he : |(k : ℝ)^2-(m : ℝ)^2| = s*d := by
    rw [sq_sub_sq,abs_mul,abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ)+(m : ℝ))]
  have hrhs : (1+(n : ℝ)^2)*(1/(m : ℝ)+1/d) =
      ((1+(n : ℝ)^2)*(d+(m : ℝ)))/((m : ℝ)*d) := by field_simp
  rw [he]
  change ((k : ℝ)^2+(n : ℝ)^2)/((m : ℝ)*(s*d)) ≤ _
  rw [hrhs]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ ((1+(n : ℝ)^2)*s*(d+(m : ℝ)))*((m : ℝ)*d) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by ring

end NLS.KdV
