import NLS.KdV.PseudomeasureLocalization
import NLS.ComplexAnalysis.ZeroCountComparison

/-! # Two zeros of the actual endpoint Hill determinant

The disc has the source radius 4*sqrt(n) and lies in the corrected closed
strip. The actual determinant has exactly two zeros counted by analytic
orders there and on the entire strip. Algebraic multiplicity of the physical
operator is not identified with analytic order in this module.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- The endpoint weight at the double resonant frequency has controlled growth. -/
theorem sobolev_two_mode_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) : Weight.sobolev r (2*(n:ℤ)) ≤ 3*(n:ℝ)^r := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by positivity
  have h3 : (3:ℝ)^r ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) (by linarith : r ≤ 1)
  simp only [Weight.sobolev_apply, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    abs_of_nonneg (show 0 ≤ 2*(n:ℝ) by positivity)]
  calc
    _ ≤ (3*(n:ℝ))^r := Real.rpow_le_rpow (by positivity) (by linarith) hr
    _ = (3:ℝ)^r*(n:ℝ)^r := Real.mul_rpow (by norm_num) hn0
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hn0 r)

/-- The proved source half-contraction cutoff makes the two effective
columns small compared with sqrt(n), without an additional cutoff premise. -/
theorem endpoint_effective_column_small (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    2*Weight.sobolev r (2*(n:ℤ))*‖q‖ ≤ Real.sqrt (n:ℝ)/8 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hC : 24 ≤ endpointHillConstant r := by
    calc
      24 = endpointHillConstant 0 := by norm_num [endpointHillConstant]
      _ ≤ _ := endpointHillConstant_mono hr hr1
  have hb : 24*((n:ℝ)^(r-1/2)*‖q‖) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right hC (by positivity)).trans (by simpa only [mul_assoc] using hs)
  have hb2 := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (n:ℝ))
  have hp : (n:ℝ)^(r-1/2)*Real.sqrt (n:ℝ) = (n:ℝ)^r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos, show r-1/2+(1/2:ℝ) = r by ring]
  have hb3 : 24*(n:ℝ)^r*‖q‖ ≤ (1/2:ℝ)*Real.sqrt (n:ℝ) := by
    calc
      _ = (24*((n:ℝ)^(r-1/2)*‖q‖))*Real.sqrt (n:ℝ) := by rw [← hp]; ring
      _ ≤ _ := hb2
  have hS := mul_le_mul_of_nonneg_right (sobolev_two_mode_le r hr hr1 n hn) (norm_nonneg q)
  nlinarith

/-- The source disc lies wholly inside the corrected strip. -/
theorem endpointHillDisc_subset_strip (n : ℕ) (hn : 1 ≤ n) :
    closedBall (freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ)) ⊆ reducedHillStrip n := by
  intro z hz
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hS : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hd : ‖z-(freeHillValue n:ℂ)‖ ≤ 4*Real.sqrt (n:ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hR : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n:ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  change |z.re-freeHillValue n| ≤ 6*(n:ℝ)
  linarith

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The actual determinant is analytic on a neighborhood of every closed-strip point. -/
theorem analyticOnNhd_endpointReducedDeterminant_spectral :
    AnalyticOnNhd ℂ (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (reducedHillStrip n) := by
  intro z hz
  exact (analyticAt_endpointReducedDeterminant r hr hr1 n hn (q,z) hz hs).comp
    (f := fun z : ℂ => (q,z)) (analyticAt_const.prod analyticAt_id)

include hn hs in
/-- Every actual determinant zero on the strip is localized, before any
choice of spectral labels or individual roots. -/
theorem endpointReducedDeterminant_zero_localization (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : endpointReducedDeterminant r hr hr1 n (q,z) = 0) :
    ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  have hf := (endpointReducedDeterminant_eq_zero_iff r hr hr1 n hn (q,z) hz hs).mp hd
  obtain ⟨u,hu0,hu⟩ := (exists_singularHillEigenvector_iff r hr hr1 n hn z hz q hs).mp hf
  have hL := endpointHillReduced_kernel_localization r hr hr1 n hn z hz q hs u hu0 hu
  have hM := endpoint_effective_column_small r hr hr1 n hn q hs
  linarith

include hn hs in
/-- Exactly two roots in the source disc, including repeated or colliding
roots and zero potential; the count is by analytic orders. -/
theorem endpointReducedDeterminant_two_zeros :
    ComplexAnalysis.analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z))
      (closedBall (freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ))) = 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hspos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hM := endpoint_effective_column_small r hr hr1 n hn q hs
  apply ComplexAnalysis.analyticZeroCount_eq_degree_of_boundary_lt 2 (by positivity)
    ((analyticOnNhd_endpointReducedDeterminant_spectral r hr hr1 n hn q hs).mono
      (endpointHillDisc_subset_strip n hn))
  intro z hz
  have hzS := endpointHillDisc_subset_strip n hn (sphere_subset_closedBall hz)
  have hrad : ‖z-(freeHillValue n:ℂ)‖ = 4*Real.sqrt (n:ℝ) := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  have he := endpointReducedDeterminant_free_error_le r hr hr1 n hn z hzS q hs
  rw [hrad] at he
  rw [norm_pow, hrad]
  have hW := (Weight.sobolev r).positive (2*(n:ℤ))
  have hP := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 2*(4*Real.sqrt (n:ℝ)))
  have hQ := mul_nonneg (sub_nonneg.mpr hM)
    (show 0 ≤ Real.sqrt (n:ℝ)/8 + 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ by positivity)
  nlinarith [sq_pos_of_pos hspos]

include hn hs in
/-- The same two analytic zeros exhaust the entire unbounded closed strip. -/
theorem endpointReducedDeterminant_strip_two_zeros :
    ComplexAnalysis.analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z))
      (reducedHillStrip n) = 2 := by
  have he : ComplexAnalysis.analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z))
      (reducedHillStrip n) =
    ComplexAnalysis.analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z))
      (closedBall (freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ))) := by
    apply ComplexAnalysis.analyticZeroCount_congr_set
    intro z hd
    constructor
    · intro hz
      have hL := endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs z hz hd
      change dist z (freeHillValue n:ℂ) ≤ 4*Real.sqrt (n:ℝ)
      rw [dist_eq_norm]
      linarith [Real.sqrt_nonneg (n:ℝ)]
    · exact fun hz => endpointHillDisc_subset_strip n hn hz
  rw [he]
  exact endpointReducedDeterminant_two_zeros r hr hr1 n hn q hs

end NLS.KdV
