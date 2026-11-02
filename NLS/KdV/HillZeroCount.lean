import NLS.KdV.HillLocalization
import NLS.ComplexAnalysis.ZeroCountComparison
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant

/-!
# Two analytic zeros in a high Hill strip

A quantitative two-dimensional determinant estimate compares the actual
Hill determinant to `(z-pi²*n²)^2`. Rouché's theorem then counts two zeros
with their analytic orders. The explicit cutoff here is `n >= 16*norm(q)`.
The relation of analytic determinant orders to operator algebraic
multiplicities is not part of this zero-count theorem.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- Quantitative comparison with the squared free dispersion determinant. -/
theorem hillReducedDeterminant_free_error_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖hillReducedDeterminant SpectralWeight.one n (q,z) - (z-(freeHillValue n : ℂ))^2‖ ≤
      8*‖z-(freeHillValue n : ℂ)‖*‖q‖ + 32*‖q‖^2 := by
  rw [hillReducedDeterminant_eq SpectralWeight.one n hn (q,z) hz hcut]
  let E := (hillModeCoordinates SpectralWeight.one.toWeight 2 n).comp
    (hillEffectivePotential SpectralWeight.one q n hn z hz hcut)
  have h1 : ‖E (1,0)‖ ≤ 4*‖q‖ := by
    simp only [E, ContinuousLinearMap.comp_apply]
    simpa only [show ‖((1,0) : ℂ × ℂ)‖ = 1 by simp, mul_one] using
      norm_hillEffectiveCorrection_one_le q n hn z hz hcut (1,0)
  have h2 : ‖E (0,1)‖ ≤ 4*‖q‖ := by
    simp only [E, ContinuousLinearMap.comp_apply]
    simpa only [show ‖((0,1) : ℂ × ℂ)‖ = 1 by simp, mul_one] using
      norm_hillEffectiveCorrection_one_le q n hn z hz hcut (0,1)
  have h := FiniteSpectralDeterminant.determinant_shift_bound E (z-(freeHillValue n : ℂ)) (4*‖q‖) (by positivity) h1 h2
  change ‖((z-(freeHillValue n : ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ)-E).toLinearMap.det -
    (z-(freeHillValue n : ℂ))^2‖ ≤ _
  convert h using 1
  ring

theorem hillClosedBall_subset_openStrip (n : ℕ) (hn : 1 ≤ n) :
    closedBall (freeHillValue n : ℂ) (n : ℝ) ⊆ openHillStrip n := by
  intro z hz
  have hd : ‖z-(freeHillValue n : ℂ)‖ ≤ (n : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue n : ℂ))
  change |z.re-freeHillValue n| < 6*(n : ℝ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  linarith

/-- The actual determinant has exactly two zeros, counting analytic orders,
in the radius-n disc, including at zero potential and at colliding roots. -/
theorem hillReducedDeterminant_two_zeros
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ComplexAnalysis.analyticZeroCount (fun z => hillReducedDeterminant SpectralWeight.one n (q,z))
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) = 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcut' : 8*‖q‖ ≤ (n : ℝ) := by linarith [norm_nonneg q]
  apply ComplexAnalysis.analyticZeroCount_eq_degree_of_boundary_lt 2 hnpos
    ((analyticOnNhd_hillReducedDeterminant_spectral SpectralWeight.one q n hn hcut').mono
      (hillClosedBall_subset_openStrip n hn))
  intro z hz
  have hz' := openHillStrip_subset n (hillClosedBall_subset_openStrip n hn (sphere_subset_closedBall hz))
  have hr : ‖z-(freeHillValue n : ℂ)‖ = (n : ℝ) := by simpa only [mem_sphere, dist_eq_norm] using hz
  have he := hillReducedDeterminant_free_error_le q n hn z hz' hcut'
  rw [hr] at he
  rw [norm_pow, hr]
  have hsq : 0 < (n : ℝ)^2 := sq_pos_of_pos hnpos
  have hprod := mul_le_mul_of_nonneg_right hcut hnpos.le
  have hquad := mul_nonneg (sub_nonneg.mpr hcut)
    (show 0 ≤ (n : ℝ)+16*‖q‖ by positivity)
  nlinarith

/-- Localization shows that the same two zeros exhaust the whole closed
high-frequency strip; no additional zeros can lie in its unbounded part. -/
theorem hillReducedDeterminant_strip_two_zeros
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    ComplexAnalysis.analyticZeroCount (fun z => hillReducedDeterminant SpectralWeight.one n (q,z))
      (reducedHillStrip n) = 2 := by
  have hcut' : 8*‖q‖ ≤ (n : ℝ) := by linarith [norm_nonneg q]
  have he : ComplexAnalysis.analyticZeroCount
      (fun z => hillReducedDeterminant SpectralWeight.one n (q,z)) (reducedHillStrip n) =
      ComplexAnalysis.analyticZeroCount (fun z => hillReducedDeterminant SpectralWeight.one n (q,z))
        (closedBall (freeHillValue n : ℂ) (n : ℝ)) := by
    apply ComplexAnalysis.analyticZeroCount_congr_set
    intro z hd
    constructor
    · intro hz
      have hloc := hillReducedDeterminant_zero_localization q n hn z hz hcut' hd
      change dist z (freeHillValue n : ℂ) ≤ (n : ℝ)
      rw [dist_eq_norm]
      linarith [norm_nonneg q]
    · exact fun hz => openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hz)
  rw [he]
  exact hillReducedDeterminant_two_zeros q n hn hcut

end NLS.KdV
