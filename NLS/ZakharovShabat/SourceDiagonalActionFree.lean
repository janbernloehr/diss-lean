import NLS.ZakharovShabat.SourceDiagonalActionRoot
import NLS.ZakharovShabat.DeletedPeriodicFree

/-! # Exact free normalization of the physical action scaling

All selected gaps are closed at the zero source. The already regularized
physical ratio is then one over twice the actual free midpoint pi*n.
This fixes the Fourier scale of the Cartesian map, including its sign.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDiagonalActionRatio_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceDiagonalActionRatio hp hp1 n (0 : CoeffPair p) = (2*(Real.pi : ℂ)*n)⁻¹ := by
  let φ : realDiagonalSourceLocus p := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0 := by
    simpa only [φ,map_zero] using canonicalPeriodicGap_zero hp hp1 n
  have h := sourceDiagonalActionRatio_zeroGap hp hp1 φ n hg
  simpa only [φ,sourceStandardRootMidpoint,map_zero,canonicalPeriodicMidpoint_zero,mul_assoc] using h

/-- The physical free scaling is the positive real inverse-square-root
frequency, with the factor two retained. -/
theorem sourceDiagonalActionRoot_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (hn : 0 < n) :
    sourceDiagonalActionRoot hp hp1 n (0 : CoeffPair p) =
      (Real.sqrt ((2*Real.pi*(n : ℝ))⁻¹) : ℂ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold sourceDiagonalActionRoot
  rw [sourceDiagonalActionRatio_zero]
  have he : (2*(Real.pi : ℂ)*n)⁻¹ = (((2*Real.pi*(n : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.sqrt_of_nonneg (by exact_mod_cast (inv_nonneg.mpr (by positivity : 0 ≤ 2*Real.pi*(n : ℝ))))]
  rfl

theorem sourceDiagonalActionRoot_zero_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (hn : 0 < n) :
    sourceDiagonalActionRoot hp hp1 n (0 : CoeffPair p) ≠ 0 := by
  rw [sourceDiagonalActionRoot_zero hp hp1 n hn]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  apply inv_pos.mpr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

end NLS.ZakharovShabat
