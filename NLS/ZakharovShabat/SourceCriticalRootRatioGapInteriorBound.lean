import NLS.ZakharovShabat.SourceCriticalRootRatioRealGapBound

/-! # Local bounds near the interior of a real gap

The transverse domination estimate is bounded on a smaller rectangle
around each interior point, on both sides of the cut simultaneously.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual quotient is locally bounded off the real axis near any
interior point of a real spectral gap. -/
theorem exists_sourceCriticalRootRatio_gapInterior_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    ∃ ε M : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < M ∧ ∀ z : ℂ, z.im ≠ 0 → ‖z-(x:ℂ)‖ ≤ ε →
      ‖deriv (canonicalDiscriminant hp (periodOnePotential φ)) z /
        sourceCanonicalRoot hp hp1 φ z‖ ≤ M := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  obtain ⟨ε,M,hε,hM,hbound⟩ := exists_sourceCriticalRootRatio_realGap_domination hp hp1 φ hφ n (hx.1.trans hx.2)
  let d := (x-a)/2
  let e := (b-x)/2
  have hd : 0 < d := by dsimp [d]; linarith [hx.1]
  have he : 0 < e := by dsimp [e]; linarith [hx.2]
  have hs : 0 < Real.sqrt (d*e) := Real.sqrt_pos.mpr (mul_pos hd he)
  refine ⟨min ε (min 1 (min d e)), M / Real.sqrt (d*e),
    lt_min hε (lt_min zero_lt_one (lt_min hd he)),
    (min_le_right _ _).trans (min_le_left _ _), div_pos hM hs, ?_⟩
  intro z hz hzε
  have hzε₀ := hzε.trans (min_le_left _ _)
  have hz₁ := hzε.trans (min_le_right _ _)
  have hzd := (hz₁.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hze := (hz₁.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hre : |z.re-x| ≤ ‖z-(x:ℂ)‖ := by
    simpa only [sub_re,ofReal_re] using Complex.abs_re_le_norm (z-(x:ℂ))
  have him : |z.im| ≤ ‖z-(x:ℂ)‖ := by
    simpa only [sub_im,ofReal_im,sub_zero] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hleft : d ≤ z.re-a := by
    have h := (abs_le.mp (hre.trans hzd)).1
    dsimp [d] at *
    linarith
  have hright : e ≤ b-z.re := by
    have h := (abs_le.mp (hre.trans hze)).2
    dsimp [e] at *
    linarith
  have hzab : z.re ∈ Ioo a b := ⟨by linarith,by linarith⟩
  have hq := hbound z.re hzab z.im hz (him.trans hzε₀)
  rw [Complex.re_add_im] at hq
  exact hq.trans (div_le_div_of_nonneg_left hM.le hs
    (Real.sqrt_le_sqrt (mul_le_mul hleft hright he.le (hd.le.trans hleft))))

end NLS.ZakharovShabat
