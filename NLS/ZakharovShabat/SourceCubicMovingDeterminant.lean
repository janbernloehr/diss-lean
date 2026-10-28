import NLS.ZakharovShabat.SourceCubicMovingCenter
import NLS.ZakharovShabat.SourceResonantDeterminant

/-! # The actual determinant at cubic distances from its center

Supporting estimates for the unresolved final weighted gap sum on p.44.
The actual counted-root gap still needs comparison with the coefficient sum.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceCubicMovingDeterminantFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- A fixed complex displacement measured in cubic amplitude from the actual diagonal center. -/
def sourceCubicShiftedCenter (n : ℤ) (t : ℂ) (s : ℝ) : ℂ := sourceCubicDiagonalCenter n s+(s : ℂ)^3*t

/-- Each cubically shifted center tends to the free center. -/
theorem sourceCubicShiftedCenter_tendsto (n : ℤ) (t : ℂ) :
    Tendsto (sourceCubicShiftedCenter n t) (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ)*n)) := by
  have hc : Continuous (fun s : ℝ => (s : ℂ)^3*t) := by fun_prop
  have ht : Tendsto (fun s : ℝ => (s : ℂ)^3*t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  unfold sourceCubicShiftedCenter
  simpa only [add_zero] using (sourceCubicDiagonalCenter_tendsto n).add ht

/-- Each fixed cubic displacement eventually stays inside the refined disk. -/
theorem sourceCubicShiftedCenter_eventually_disk (n : ℤ) (t : ℂ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sourceCubicShiftedCenter n t s ∈ refinedResonantDisk n :=
  (sourceCubicShiftedCenter_tendsto n t).eventually (Metric.ball_mem_nhds _ (by positivity))

/-- The diagonal change along a cubic displacement is negligible after cubic normalization. -/
theorem sourceCubicDiagonalShiftError_tendsto (n : ℤ) (t : ℂ) :
    Tendsto (fun s : ℝ =>
      (sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicShiftedCenter n t s)-
        sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s))/(s : ℂ)^3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun s : ℝ => (sourceCubicDiagonalBound n/(Real.pi/4))*s^2*‖t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => (sourceCubicDiagonalBound n/(Real.pi/4))*s^2*‖t‖) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [weightedCubicTailFamily_eventually_controlled n,hs1,self_mem_nhdsWithin,
    sourceCubicDiagonalCenter_eventually n,sourceCubicShiftedCenter_eventually_disk n t] with s hsmall hs1 hs hc hx
  have hb := norm_diagonal_sub_le_on_refined_disk_of_bound n _ _ (sourceCubicDiagonal_analytic n n s hsmall.1)
    (sourceCubicDiagonal_norm_le n n s hs.le hs1.le hsmall.1) _ _ hx hc.1
  simp only [sourceCubicShiftedCenter,add_sub_cancel_left,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg hs.le] at hb
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply (div_le_iff₀ (pow_pos hs 3)).mpr
  exact hb.trans_eq (by ring)

/-- The normalized actual diagonal residual tends to the chosen complex displacement. -/
theorem sourceCubicDiagonalResidual_tendsto (n : ℤ) (t : ℂ) :
    Tendsto (fun s : ℝ =>
      (sourceCubicShiftedCenter n t s-(Real.pi : ℂ)*n-
        sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicShiftedCenter n t s))/(s : ℂ)^3)
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
  have ht := (sourceCubicDiagonalShiftError_tendsto n t).const_sub t
  simp only [sub_zero] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [sourceCubicDiagonalCenter_eventually n,self_mem_nhdsWithin] with s hc hs
  have he : sourceCubicDiagonalCenter n s-(Real.pi : ℂ)*n =
      sourceResonantAFunction (by simp) (sourceCubicTailFamily n s) n (sourceCubicDiagonalCenter n s) := by
    linear_combination hc.2.1
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold sourceCubicShiftedCenter
  field_simp
  linear_combination he

/-- The actual determinant near the moving center has the normalized quadratic limit; this does not yet locate or identify its roots. -/
theorem sourceCubicDeterminant_scaled_tendsto (n : ℤ) (hn : 0 < n) (t : ℂ) :
    Tendsto (fun s : ℝ => sourceResonantDeterminantFunction (by simp) (sourceCubicTailFamily n s) n
      (sourceCubicShiftedCenter n t s)/(s : ℂ)^6)
      (𝓝[>] (0 : ℝ)) (𝓝 (t^2-(2*(sourceCubicTailScale n : ℂ))^2)) := by
  have hz := (sourceCubicShiftedCenter_eventually_disk n t).mono (fun _ h => refinedResonantDisk_subset_strip n h)
  have hpos := sourceCubicMovingCoefficient_tendsto n hn true (sourceCubicShiftedCenter n t) hz (sourceCubicShiftedCenter_tendsto n t)
  have hneg := sourceCubicMovingCoefficient_tendsto n hn false (sourceCubicShiftedCenter n t) hz (sourceCubicShiftedCenter_tendsto n t)
  have h := ((sourceCubicDiagonalResidual_tendsto n t).pow 2).sub (hpos.mul hneg)
  rw [← pow_two] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold sourceResonantDeterminantFunction sourceCubicCoefficient
  simp only [if_true,Bool.false_eq_true,if_false]
  field_simp

end NLS.ZakharovShabat
