import NLS.ZakharovShabat.SourceBirkhoffCoordinates

/-! # Exact inverse normalization of eta

The actual signed eta coordinate is recovered from the original signed Birkhoff coordinate by its inverse normalization and beta phase.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Recover the actual eta coordinate by the inverse normalization and beta phase. -/
theorem sourceGapWeightedEtaCoordinate_eq_inverse_normalization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) (ψ : CoeffPair p)
    (hξ : sourceNormalizedActionRoot hp hp1 n ψ ≠ 0) :
    sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ =
      (sourceNormalizedActionRoot hp hp1 n ψ)⁻¹*sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ*
        exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s ψ) := by
  rw [sourceBirkhoffWeightedCoordinate]
  rw [← mul_assoc,← mul_assoc,inv_mul_cancel₀ hξ,one_mul,mul_assoc,← exp_add]
  have he : sign*I*sourceAngularBetaCorrection hp hp1 n s ψ+
      -sign*I*sourceAngularBetaCorrection hp hp1 n s ψ = 0 := by ring
  rw [he,exp_zero,mul_one]

/-- The actual signed coordinate is a fixed linear combination of the rectangular ones. -/
theorem sourceBirkhoffWeightedCoordinate_eq_rectangular
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) (ψ : CoeffPair p)
    (hsign : sign = 1 ∨ sign = -1) :
    sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ =
      ((Real.sqrt 8:ℂ)/2)*(sourceBirkhoffX hp hp1 n s ψ+sign*I*sourceBirkhoffY hp hp1 n s ψ) := by
  have hn : (Real.sqrt 8:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  rcases hsign with rfl | rfl <;> simp only [sourceBirkhoffX,sourceBirkhoffY] <;> field_simp [hn] <;> ring

/-- Scalar inverse bounds transfer rectangular estimates to the actual eta coordinate. -/
theorem norm_sourceGapWeightedEta_le_rectangular
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (sign : ℂ) (ψ : CoeffPair p)
    (hsign : sign = 1 ∨ sign = -1) (A B : ℝ) (hA : 0 ≤ A)
    (hξ : sourceNormalizedActionRoot hp hp1 n ψ ≠ 0)
    (hinv : ‖(sourceNormalizedActionRoot hp hp1 n ψ)⁻¹‖ ≤ A)
    (hβ : ‖sourceAngularBetaCorrection hp hp1 n s ψ‖ ≤ B) :
    ‖sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ‖ ≤
      (A*(Real.sqrt 8/2)*Real.exp B)*(‖sourceBirkhoffX hp hp1 n s ψ‖+‖sourceBirkhoffY hp hp1 n s ψ‖) := by
  have hs : ‖sign‖ = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hb : ‖exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s ψ)‖ ≤ Real.exp B := by
    apply (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    simpa only [norm_mul,norm_neg,norm_I,hs,one_mul,mul_one] using hβ
  have hz : ‖sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ‖ ≤
      (Real.sqrt 8/2)*(‖sourceBirkhoffX hp hp1 n s ψ‖+‖sourceBirkhoffY hp hp1 n s ψ‖) := by
    rw [sourceBirkhoffWeightedCoordinate_eq_rectangular hp hp1 n s sign ψ hsign,norm_mul]
    have hn : ‖(Real.sqrt 8:ℂ)/2‖ = Real.sqrt 8/2 := by
      simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      norm_num
    rw [hn]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [norm_mul,hs,norm_I,one_mul] using
      norm_add_le (sourceBirkhoffX hp hp1 n s ψ) (sign*I*sourceBirkhoffY hp hp1 n s ψ)
  rw [sourceGapWeightedEtaCoordinate_eq_inverse_normalization hp hp1 n s sign ψ hξ,norm_mul,norm_mul]
  exact (mul_le_mul (mul_le_mul hinv hz (norm_nonneg _) hA) hb (norm_nonneg _) (by positivity)).trans_eq (by ring)

end NLS.ZakharovShabat
