import NLS.ZakharovShabat.SourceRealHigherAction

/-! # Mean-value comparisons relative to any odd action level

The base action contributes a nonnegative spectral weight to the gap measure.
The mean-value identity therefore remains valid without dividing by that action,
even for collapsed gaps or gaps meeting the spectral origin.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Mean-value comparison to an arbitrary odd base level, with no nonvanishing hypothesis. -/
theorem sourceRealHigherAction_eq_power_mul_even_level (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (l k : ℕ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      sourceRealHigherAction hp hp1 φ n (2*l+k) =
        ζ^k*sourceRealHigherAction hp hp1 φ n (2*l) := by
  let z := fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  let g := fun θ => z θ^(2*l)*(Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ)
  have hz : Continuous z := by dsimp [z,realGapAffinePoint]; fun_prop
  have hg : Continuous g := (hz.pow _).mul
    (Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n))
  have hnon : ∀ θ ∈ uIoc (0:ℝ) Real.pi, 0 ≤ g θ := by
    intro θ hθ
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    dsimp [g]
    apply mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  obtain ⟨θ,_,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := MeasureTheory.volume)
    (hz.pow k).continuousOn (hg.intervalIntegrable 0 Real.pi) hnon
  simp only [Pi.pow_apply] at he
  refine ⟨z θ,realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ,?_⟩
  have hint : (∫ t in (0:ℝ)..Real.pi, z t^(2*l+k)*
      (Real.sin t*sourceRealGapCosineProfile hp hp1 φ.val n t)) =
      z θ^k*(∫ t in (0:ℝ)..Real.pi, g t) := by
    rw [← he]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [g]
    rw [pow_add]
    ring
  change _ = z θ^k*_
  unfold sourceRealHigherAction
  change _*(∫ t in (0:ℝ)..Real.pi, z t^(2*l+k)*
    (Real.sin t*sourceRealGapCosineProfile hp hp1 φ.val n t)) = _
  rw [hint]
  dsimp [g,z]
  ring

/-- An absolute bound on the gap controls every even increment of an odd action level. -/
theorem sourceRealHigherAction_even_level_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (l k : ℕ) (B : ℝ)
    (hB : ∀ ζ ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      |ζ| ≤ B) :
    sourceRealHigherAction hp hp1 φ n (2*l+2*k) ≤
      B^(2*k)*sourceRealHigherAction hp hp1 φ n (2*l) := by
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_even_level hp hp1 φ n l (2*k)
  rw [he,← pow_abs_two_mul ζ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg ζ) (hB ζ hζ) _)
    (sourceRealHigherAction_even_nonneg hp hp1 φ n l)

end NLS.ZakharovShabat
