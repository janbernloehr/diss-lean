import NLS.ZakharovShabat.ResonantDeterminantLocalization
import NLS.ZakharovShabat.ResonantCauchyGap

/-!
# The actual off-diagonal product supremum and root gap

The full-strip product supremum is finite under the uniform coefficient
bounds. Any two actual determinant zeros in the strip satisfy the source
factor-six gap estimate. This does not presume existence of two distinct
zeros, or identify scalar zero orders with spectral multiplicities.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source full-strip supremum `|b_n⁺ b_n⁻|_{U_n}`. -/
def resonantBProductSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  weightedStripSup SpectralWeight.one n (fun z =>
    weightedResonantBPlusExtension hp w φ n z * weightedResonantBMinusExtension hp w φ n z)

/-- The full-strip product supremum is nonnegative, bounded, and dominates every value. -/
theorem resonantBProductSup_bounds (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (hb : ∀ z ∈ resonantStrip n,
      ‖weightedResonantBMinusExtension hp w φ n z‖ ≤ Real.pi/16 ∧
      ‖weightedResonantBPlusExtension hp w φ n z‖ ≤ Real.pi/16) :
    0 ≤ resonantBProductSup hp w φ n ∧ resonantBProductSup hp w φ n ≤ (Real.pi/16)^2 ∧
      ∀ z ∈ resonantStrip n,
        ‖weightedResonantBPlusExtension hp w φ n z * weightedResonantBMinusExtension hp w φ n z‖ ≤
          resonantBProductSup hp w φ n := by
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      SpectralWeight.one (2*n) * ‖weightedResonantBPlusExtension hp w φ n z *
        weightedResonantBMinusExtension hp w φ n z‖ ≤ (Real.pi/16)^2 := by
    simp only [SpectralWeight.one_apply, one_mul, norm_mul, pow_two]
    exact mul_le_mul (hb z hz).2 (hb z hz).1 (norm_nonneg _) (by positivity)
  simpa only [resonantBProductSup, SpectralWeight.one_apply, one_mul] using
    weightedStripSup_bounds SpectralWeight.one n _ _ hpoint

/-- Any two actual strip zeros satisfy the branch-free factor-six gap estimate. -/
theorem resonantDeterminant_root_gap_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w φ n) (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖weightedResonantAExtension hp w φ n z‖ ≤ Real.pi/32 ∧
      ‖weightedResonantBMinusExtension hp w φ n z‖ ≤ Real.pi/16 ∧
      ‖weightedResonantBPlusExtension hp w φ n z‖ ≤ Real.pi/16)
    (x y : ℂ) (hx : x ∈ resonantStrip n) (hy : y ∈ resonantStrip n)
    (hx0 : resonantDeterminantExtension hp w φ n x = 0)
    (hy0 : resonantDeterminantExtension hp w φ n y = 0) :
    ‖x-y‖^2 ≤ 6 * resonantBProductSup hp w φ n := by
  have hsup := resonantBProductSup_bounds hp w φ n (fun z hz => (hb z hz).2)
  have hdisk (z : ℂ) (hz : z ∈ resonantStrip n) (hz0 : resonantDeterminantExtension hp w φ n z = 0) :
      z ∈ refinedResonantDisk n := by
    have h := norm_resonant_quadratic_root_le (z - (Real.pi : ℂ)*n)
      (weightedResonantAExtension hp w φ n z) (weightedResonantBPlusExtension hp w φ n z)
      (weightedResonantBMinusExtension hp w φ n z) (hb z hz).1 (hb z hz).2.2 (hb z hz).2.1 hz0
    change dist z ((Real.pi : ℂ)*n) < Real.pi/4
    rw [dist_eq_norm]
    exact h.trans_lt (by linarith [Real.pi_pos])
  have hresidual (z : ℂ) (hz : z ∈ resonantStrip n) (hz0 : resonantDeterminantExtension hp w φ n z = 0) :
      ‖z - (Real.pi : ℂ)*n - weightedResonantAExtension hp w φ n z‖^2 ≤ resonantBProductSup hp w φ n := by
    have he : ‖z - (Real.pi : ℂ)*n - weightedResonantAExtension hp w φ n z‖^2 =
        ‖weightedResonantBPlusExtension hp w φ n z * weightedResonantBMinusExtension hp w φ n z‖ := by
      rw [← norm_pow]
      exact congrArg norm (sub_eq_zero.mp hz0)
    exact he.trans_le (hsup.2.2 z hz)
  exact norm_gap_sq_le_of_residual_bounds ((Real.pi : ℂ)*n) x y (weightedResonantAExtension hp w φ n) _
    (norm_diagonal_sub_le_on_refined_disk n _ ha (fun z hz => (hb z hz).1)
      x y (hdisk x hx hx0) (hdisk y hy hy0)) (hresidual x hx hx0) (hresidual y hy hy0)

/-- The Cauchy derivative estimate and actual root-gap estimate hold locally uniformly. -/
theorem exists_uniform_resonantRoot_gap (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        (∀ z ∈ refinedResonantDisk n, ‖deriv (weightedResonantAExtension hp w ψ n) z‖ ≤ 1/8) ∧
        (0 ≤ resonantBProductSup hp w ψ n ∧ resonantBProductSup hp w ψ n ≤ (Real.pi/16)^2) ∧
        ∀ x ∈ resonantStrip n, ∀ y ∈ resonantStrip n,
          resonantDeterminantExtension hp w ψ n x = 0 → resonantDeterminantExtension hp w ψ n y = 0 →
            ‖x-y‖^2 ≤ 6 * resonantBProductSup hp w ψ n := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_resonantDeterminant_control hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn
  have ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w ψ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_weightedResonantAExtension hp w n (ψ,z) ((hb n hn).1 ⟨hψ,hz⟩)).comp
      (analyticAt_const.prod analyticAt_id)
  have hbounds (z : ℂ) (hz : z ∈ resonantStrip n) := ((hb n hn).2 ψ hψ z hz).2
  have hsup := resonantBProductSup_bounds hp w ψ n (fun z hz => (hbounds z hz).2)
  exact ⟨norm_deriv_le_on_refined_disk n _ ha (fun z hz => (hbounds z hz).1), ⟨hsup.1,hsup.2.1⟩,
    fun x hx y hy hx0 hy0 => resonantDeterminant_root_gap_le hp w ψ n ha hbounds x y hx hy hx0 hy0⟩

end NLS.ZakharovShabat
