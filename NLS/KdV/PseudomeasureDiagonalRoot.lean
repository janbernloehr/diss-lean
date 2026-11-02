import NLS.KdV.PseudomeasureSpectralLipschitz
import NLS.FunctionalAnalysis.ContractingSelection
import Mathlib.Topology.MetricSpace.Contracting

/-! The actual scalar diagonal root of the original singular Hill reduction. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal NNReal
namespace NLS.KdV

/-- The verified physical cutoff also leaves ample room inside the spectral strip. -/
theorem endpointHill_norm_le_index_sixteenth (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) : ‖q‖ ≤ (n:ℝ)/16 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hS : 1 ≤ Weight.sobolev r (2*(n:ℤ)) :=
    Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) hr
  have hM := endpoint_effective_column_small r hr hr1 n hn q hs
  have hSQ : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  nlinarith [mul_le_mul_of_nonneg_right hS (norm_nonneg q)]

/-- The actual diagonal is uniformly bounded on the WHOLE corrected strip. -/
theorem norm_endpointDiagonal_le_two_norm (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) : ‖endpointDiagonal r hr hr1 n (q,z)‖ ≤ 2*‖q‖ := by
  have h0 : ‖q.val 0‖ ≤ ‖q‖ := by
    simpa only [SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply,
      Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero, Real.one_rpow, div_one] using
      WeightedCoeff.norm_apply_le (SpectralWeight.one.negativeSobolev r) ⊤ q 0
  have he := endpointDiagonal_error_le r hr hr1 n hn z hz q hs
  have ht := norm_le_norm_sub_add (endpointDiagonal r hr hr1 n (q,z)) (q.val 0)
  have hscale := mul_le_mul_of_nonneg_right hs (norm_nonneg q)
  nlinarith

/-- The common fixed-point disk is contained strictly in the corrected physical strip. -/
theorem diagonalRoot_disk_interior (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ closedBall (freeHillValue n:ℂ) (2*‖q‖)) :
    |z.re-freeHillValue n| < 6*(n:ℝ) := by
  have hloc : ‖z-(freeHillValue n:ℂ)‖ ≤ 2*‖q‖ := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hRe := (Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))).trans hloc
  simp only [Complex.sub_re, Complex.ofReal_re] at hRe
  have hq := endpointHill_norm_le_index_sixteenth r hr hr1 n hn q hs
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Banach contraction constructs the actual original diagonal root; none is supplied as data. -/
theorem exists_endpointHillDiagonalRoot (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ∃ a : ℂ, a ∈ reducedHillStrip n ∧
      a = (freeHillValue n:ℂ)+endpointDiagonal r hr hr1 n (q,a) ∧
      ‖a-(freeHillValue n:ℂ)‖ ≤ 2*‖q‖ := by
  let B := closedBall (freeHillValue n:ℂ) (2*‖q‖)
  let F : ℂ → ℂ := fun z => (freeHillValue n:ℂ)+endpointDiagonal r hr hr1 n (q,z)
  have hstrip (z : ℂ) (hz : z ∈ B) : z ∈ reducedHillStrip n :=
    (diagonalRoot_disk_interior r hr hr1 n hn q hs z hz).le
  have hmap : MapsTo F B B := by
    intro z hz
    change dist (F z) (freeHillValue n:ℂ) ≤ 2*‖q‖
    rw [dist_eq_norm]
    simpa only [F, add_sub_cancel_left] using norm_endpointDiagonal_le_two_norm r hr hr1 n hn q hs z (hstrip z hz)
  have hc : ContractingWith (1/8:ℝ≥0) (hmap.restrict F B B) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (F x.val) (F y.val) ≤ ((1/8:ℝ≥0):ℝ)*dist x.val y.val
    rw [show ((1/8:ℝ≥0):ℝ) = (1/8:ℝ) by norm_num, dist_eq_norm, dist_eq_norm]
    simpa only [F, add_sub_add_left_eq_sub] using
      endpointDiagonal_sub_le_eighth r hr hr1 n hn x.val y.val (hstrip x.val x.property)
        (hstrip y.val y.property) q hs
  have hcenter : (freeHillValue n:ℂ) ∈ B := by simp only [B, mem_closedBall, dist_self]; positivity
  obtain ⟨a, ha, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    (show IsComplete B from isClosed_closedBall.isComplete) hmap hc hcenter (edist_ne_top _ _)
  refine ⟨a, hstrip a ha, hfix.symm, ?_⟩
  simpa only [B, mem_closedBall, dist_eq_norm] using ha

/-- Intrinsic total diagonal-root function; its root property is used only
under the explicit verified cutoff. The fallback is never used in that region. -/
def endpointHillDiagonalRoot (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) : ℂ :=
  if hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 then
    Classical.choose (exists_endpointHillDiagonalRoot r hr hr1 n hn q hs) else (freeHillValue n:ℂ)

theorem endpointHillDiagonalRoot_spec (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillDiagonalRoot r hr hr1 n hn q ∈ reducedHillStrip n ∧
      endpointHillDiagonalRoot r hr hr1 n hn q = (freeHillValue n:ℂ)+
        endpointDiagonal r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q) ∧
      ‖endpointHillDiagonalRoot r hr hr1 n hn q-(freeHillValue n:ℂ)‖ ≤ 2*‖q‖ := by
  rw [endpointHillDiagonalRoot, dif_pos hs]
  exact Classical.choose_spec (exists_endpointHillDiagonalRoot r hr hr1 n hn q hs)

/-- Every constructed root lies strictly inside the corrected spectral strip. -/
theorem endpointHillDiagonalRoot_interior (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    |(endpointHillDiagonalRoot r hr hr1 n hn q).re-freeHillValue n| < 6*(n:ℝ) := by
  apply diagonalRoot_disk_interior r hr hr1 n hn q hs
  rw [mem_closedBall, dist_eq_norm]
  exact (endpointHillDiagonalRoot_spec r hr hr1 n hn q hs).2.2

/-- Uniqueness is on the ENTIRE corrected strip, not merely the fixed-point disk. -/
theorem endpointHillDiagonalRoot_unique (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (a : ℂ) (ha : a ∈ reducedHillStrip n)
    (he : a = (freeHillValue n:ℂ)+endpointDiagonal r hr hr1 n (q,a)) :
    a = endpointHillDiagonalRoot r hr hr1 n hn q := by
  obtain ⟨hstrip, hroot, _⟩ := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs
  have hLip := endpointDiagonal_sub_le_eighth r hr hr1 n hn a
    (endpointHillDiagonalRoot r hr hr1 n hn q) ha hstrip q hs
  have hd : a-endpointHillDiagonalRoot r hr hr1 n hn q = endpointDiagonal r hr hr1 n (q,a)-
      endpointDiagonal r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q) := by
    linear_combination he-hroot
  rw [← hd] at hLip
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (a-endpointHillDiagonalRoot r hr hr1 n hn q)]))

/-- The actual root retains the small original diagonal error, including the mean coefficient. -/
theorem endpointHillDiagonalRoot_error_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointHillDiagonalRoot r hr hr1 n hn q-(freeHillValue n:ℂ)-q.val 0‖ ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  obtain ⟨hstrip, hroot, _⟩ := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs
  have he := endpointDiagonal_error_le r hr hr1 n hn _ hstrip q hs
  have heq : endpointHillDiagonalRoot r hr hr1 n hn q-(freeHillValue n:ℂ) =
      endpointDiagonal r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q) := by
    linear_combination hroot
  rw [heq]
  exact he

end NLS.KdV
