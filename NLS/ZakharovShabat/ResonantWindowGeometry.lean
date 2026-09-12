import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.SpectralWeight

/-!
# Geometry of the two near-resonant windows in Lemma 6.5

Opposite physical windows only interact through the potential tail. Monotonicity
of the source weight gives the additional factor `w(n)` in the near-near term.
All cutoffs are closed, and the potential tail retains its boundary.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The closed half-radius window around the signed physical center. -/
def resonantWindow (n : ℤ) : Finset ℤ := Coeff.frequencyWindow n (n.natAbs / 2)

@[simp] theorem mem_resonantWindow (n j : ℤ) :
    j ∈ resonantWindow n ↔ (j - n).natAbs ≤ n.natAbs / 2 := Coeff.mem_frequencyWindow _ _ _

/-- The difference of opposite near frequencies belongs to the source's potential tail. -/
theorem resonantWindows_tail {n j k : ℤ} (hj : j ∈ resonantWindow n) (hk : k ∈ resonantWindow (-n)) :
    n.natAbs ≤ (j - k).natAbs := by
  simp only [mem_resonantWindow, Int.natAbs_neg] at *
  omega

/-- The output's shifted distance is bounded by the potential frequency. -/
theorem resonantWindows_output_distance {n j k : ℤ} (hj : j ∈ resonantWindow n) (hk : k ∈ resonantWindow (-n)) :
    |j - n| ≤ |j - k| := by
  have h : (j-n).natAbs ≤ (j-k).natAbs := by
    simp only [mem_resonantWindow, Int.natAbs_neg] at *
    omega
  rw [← Int.natCast_natAbs (j-n), ← Int.natCast_natAbs (j-k)]
  exact_mod_cast h

/-- The input's opposite shifted frequency is at least as large as the resonant center. -/
theorem resonantWindow_input_distance {n k : ℤ} (hk : k ∈ resonantWindow (-n)) :
    |n| ≤ |k - n| := by
  have h : n.natAbs ≤ (k-n).natAbs := by
    simp only [mem_resonantWindow, Int.natAbs_neg] at hk
    omega
  rw [← Int.natCast_natAbs n, ← Int.natCast_natAbs (k-n)]
  exact_mod_cast h

/-- The sharp weight gain in the near-near contribution of Lemma 6.5. -/
theorem resonantWindows_weight_gain (w : SpectralWeight) {n j k : ℤ}
    (hj : j ∈ resonantWindow n) (hk : k ∈ resonantWindow (-n)) :
    w (j - n) * w n ≤ w (j - k) * w (k - n) :=
  mul_le_mul (w.mono_abs (resonantWindows_output_distance hj hk))
    (w.mono_abs (resonantWindow_input_distance hk)) (w.positive n).le (w.positive (j-k)).le

/-- Dividing the weight gain gives the factor appearing in the source's tail estimate. -/
theorem resonantWindows_weight_ratio (w : SpectralWeight) {n j k : ℤ}
    (hj : j ∈ resonantWindow n) (hk : k ∈ resonantWindow (-n)) :
    w (j - n) ≤ (w (j - k) * w (k - n)) / w n :=
  (le_div_iff₀ (w.positive n)).mpr (resonantWindows_weight_gain w hj hk)

end NLS.ZakharovShabat
