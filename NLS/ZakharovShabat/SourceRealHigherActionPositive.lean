import NLS.ZakharovShabat.SourceRealHigherAction

/-! # Strict positivity of odd-level actions

The cosine integral is positive on every open real gap, including a gap
crossing zero. Even printed levels do not have this positivity argument.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every odd-level action is strictly positive when its real gap is open. -/
theorem sourceRealHigherAction_even_pos {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    0 < sourceRealHigherAction hp hp1 φ n (2*m) := by
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hwidth : 0 < (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
    simpa only [canonicalPeriodicGap,Complex.sub_re,sub_pos] using hopen
  have hex : ∃ θ ∈ Ioo 0 Real.pi, realGapAffinePoint hp hp1 φ.val n (Real.cos θ) ≠ 0 := by
    by_cases hz : realGapAffinePoint hp hp1 φ.val n 0 = 0
    · refine ⟨Real.pi/3,⟨by positivity,by linarith [Real.pi_pos]⟩,?_⟩
      rw [Real.cos_pi_div_three]
      unfold realGapAffinePoint at hz ⊢
      dsimp only at hz ⊢
      intro he
      linarith
    · exact ⟨Real.pi/2,⟨by positivity,by linarith [Real.pi_pos]⟩,by simpa using hz⟩
  have hc : Continuous (fun θ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)) := by
    unfold realGapAffinePoint
    fun_prop
  unfold sourceRealHigherAction
  apply mul_pos (div_pos hwidth Real.pi_pos)
  apply intervalIntegral.integral_pos Real.pi_pos
    ((hc.pow (2*m)).mul (Real.continuous_sin.mul
      (sourceRealGapCosineProfile_continuous hp hp1 φ n))).continuousOn
  · intro θ hθ
    apply mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (sourceRealGapCosineProfile_nonneg hp hp1 φ n θ)
  · obtain ⟨θ,hθ,hne⟩ := hex
    refine ⟨θ,⟨hθ.1.le,hθ.2.le⟩,?_⟩
    apply mul_pos
    · rw [pow_mul]
      exact pow_pos (sq_pos_of_ne_zero hne) m
    · exact mul_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
        (sourceRealGapCosineProfile_pos hp hp1 φ n hgap θ hθ)

/-- An odd-level real action vanishes exactly when its original periodic gap collapses. -/
theorem sourceRealHigherAction_even_eq_zero_iff {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    sourceRealHigherAction hp hp1 φ n (2*m) = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
  constructor
  · intro hz
    by_contra hgap
    exact (sourceRealHigherAction_even_pos hp hp1 φ n m hgap).ne' hz
  · intro hgap
    exact sourceRealHigherAction_of_collapsed hp hp1 φ n hgap (2*m)

end NLS.ZakharovShabat
