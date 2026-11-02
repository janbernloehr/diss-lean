import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral
import NLS.KdV.PseudomeasureDiagonalRootAnalytic

/-! The actual analytic diagonal root of source Lemma2.17 in original distribution norms. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The intrinsic root of the ORIGINAL physical diagonal equation. -/
def sourceDiagonalRoot (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ℂ :=
  endpointHillDiagonalRoot r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)

/-- Actual source equation,full-strip membership and original-norm localization. -/
theorem sourceDiagonalRoot_spec (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceDiagonalRoot r hr n hn q ∈ reducedHillStrip n ∧
      sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-
        (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn q)).1 = 0 ∧
      ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)‖ ≤ 2*‖q‖ := by
  have hx := endpointHillDiagonalRoot_spec r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using hs)
  refine ⟨hx.1, ?_, ?_⟩
  · have he := hx.2.1
    change endpointHillDiagonalRoot r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)-
      (freeHillValue n:ℂ)-endpointDiagonal r hr.1 hr.2 n
        (sourceEndpointCoefficients r q,endpointHillDiagonalRoot r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)) = 0
    linear_combination he
  · simpa only [sourceDiagonalRoot, norm_sourceEndpointCoefficients] using hx.2.2

/-- Every root of the literal source equation on the corrected strip is this same intrinsic root. -/
theorem sourceDiagonalRoot_unique (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (he : z-(freeHillValue n:ℂ)-(sourceEndpointEntries r hr n (q,z)).1 = 0) :
    z = sourceDiagonalRoot r hr n hn q := by
  apply endpointHillDiagonalRoot_unique r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using hs) z hz
  change z-(freeHillValue n:ℂ)-endpointDiagonal r hr.1 hr.2 n (sourceEndpointCoefficients r q,z) = 0 at he
  linear_combination he

/-- The root retains the exact source mean coefficient and the original shrinking error bound. -/
theorem sourceDiagonalRoot_error_le (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-q.val (mode 0)‖ ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  simpa only [sourceDiagonalRoot, sourceEndpointCoefficients_apply, norm_sourceEndpointCoefficients, neg_zero] using
    endpointHillDiagonalRoot_error_le r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)
      (by simpa only [norm_sourceEndpointCoefficients] using hs)

/-- Complex analyticity is in the exact original endpoint Banach norm. -/
theorem analyticAt_sourceDiagonalRoot (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    AnalyticAt ℂ (sourceDiagonalRoot r hr n hn) q := by
  have ha := analyticAt_endpointHillDiagonalRoot r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using hs)
  exact ha.comp (f := sourceEndpointCoefficientsCLM r) ((sourceEndpointCoefficientsCLM r).analyticAt q)

/-- In particular the selected original root is real analytic as required by the source. -/
theorem realAnalyticAt_sourceDiagonalRoot (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    AnalyticAt ℝ (sourceDiagonalRoot r hr n hn) q :=
  (analyticAt_sourceDiagonalRoot r hr n hn q hs).restrictScalars

/-- The SAME original diagonal root restricted to a stronger source spectral weight. -/
def sourceWeightedDiagonalRoot (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) : ℂ :=
  sourceDiagonalRoot r hr n hn (sourceForgetWeight w r q)

/-- Analyticity survives arbitrary source weights while the entire original distribution stays fixed. -/
theorem analyticAt_sourceWeightedDiagonalRoot (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    AnalyticAt ℂ (sourceWeightedDiagonalRoot w r hr n hn) q := by
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ < 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans_lt hs
  exact (analyticAt_sourceDiagonalRoot r hr n hn _ hsmall).comp
    (f := sourceForgetWeight w r) ((sourceForgetWeight w r).analyticAt q)

/-- One original norm-ball cutoff gives actual analytic roots with the source's
shrinking diagonal bound;mean-zero potentials have displacement at most R/8. -/
theorem source_uniform_diagonal_roots (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n →
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
        endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2 ∧
        AnalyticAt ℂ (sourceDiagonalRoot r hr n hn) q ∧
        sourceDiagonalRoot r hr n hn q ∈ reducedHillStrip n ∧
        sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-
          (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn q)).1 = 0 ∧
        ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-q.val (mode 0)‖ ≤
          2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 ∧
        (q.val (mode 0) = 0 → ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)‖ ≤ R/8) := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 (8*R)
  refine ⟨N, hN, fun n hn hnN q hq => ?_⟩
  let c := endpointHillConstant r*(n:ℝ)^(r-1/2)
  have hc : 0 ≤ c := by dsimp [c]; positivity [endpointHillConstant_pos r hr.2]
  have hR : 0 ≤ R := (norm_nonneg q).trans hq
  have hbound : c*R ≤ 1/16 := by
    have hh := hcut n hnN
    change c*(8*R) ≤ 1/2 at hh
    nlinarith
  have hsmall : c*‖q‖ < 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hq hc
    linarith
  obtain ⟨hstrip, he, _⟩ := sourceDiagonalRoot_spec r hr n hn q hsmall.le
  have herr : ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-q.val (mode 0)‖ ≤
      2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 := by
    apply (sourceDiagonalRoot_error_le r hr n hn q hsmall.le).trans
    have hh := mul_le_mul_of_nonneg_left (mul_self_le_mul_self (norm_nonneg q) hq)
      (show 0 ≤ 2*c by positivity)
    nlinarith
  refine ⟨hsmall, analyticAt_sourceDiagonalRoot r hr n hn q hsmall, hstrip, he, herr, ?_⟩
  intro hmean
  rw [hmean, sub_zero] at herr
  have hh := mul_le_mul_of_nonneg_right hbound hR
  nlinarith

/-- Source Lemma2.17 on B_(2m),with an explicit analytic original root and the
source displacement bound8*C_r*n^(r-1/2)*m²<=m/4. No root family is assumed. -/
theorem sourceLemma2_17 (r : ℝ) (hr : AdmissiblePredualOrder r) (m : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n →
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ 2*m → q.val (mode 0) = 0 →
        AnalyticAt ℝ (sourceDiagonalRoot r hr n hn) q ∧
        sourceDiagonalRoot r hr n hn q ∈ reducedHillStrip n ∧
        sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)-
          (sourceEndpointEntries r hr n (q,sourceDiagonalRoot r hr n hn q)).1 = 0 ∧
        ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)‖ ≤
          8*endpointHillConstant r*(n:ℝ)^(r-1/2)*m^2 ∧
        ‖sourceDiagonalRoot r hr n hn q-(freeHillValue n:ℂ)‖ ≤ m/4 ∧
        ∀ z ∈ reducedHillStrip n, z-(freeHillValue n:ℂ)-(sourceEndpointEntries r hr n (q,z)).1 = 0 →
          z = sourceDiagonalRoot r hr n hn q := by
  obtain ⟨N, hN, hroot⟩ := source_uniform_diagonal_roots r hr (2*m)
  refine ⟨N, hN, fun n hn hnN q hq hmean => ?_⟩
  obtain ⟨hqsmall, ha, hstrip, he, herr, hsmall⟩ := hroot n hn hnN q hq
  rw [hmean, sub_zero] at herr
  refine ⟨ha.restrictScalars, hstrip, he, ?_, ?_, ?_⟩
  · exact herr.trans_eq (by ring)
  · have hh := hsmall hmean
    linarith
  · exact fun z hz hzroot => sourceDiagonalRoot_unique r hr n hn q hqsmall.le z hz hzroot

/-- One cutoff chosen BEFORE BOTH the weight and original weighted potential
gives the SAME analytic physical roots and shrinking bounds in every source weight. -/
theorem source_uniform_weighted_diagonal_roots (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
        AnalyticAt ℂ (sourceWeightedDiagonalRoot w r hr n hn) q ∧
        sourceWeightedDiagonalRoot w r hr n hn q ∈ reducedHillStrip n ∧
        sourceWeightedDiagonalRoot w r hr n hn q-(freeHillValue n:ℂ)-
          (sourceEndpointEntries r hr n (sourceForgetWeight w r q,sourceWeightedDiagonalRoot w r hr n hn q)).1 = 0 ∧
        ‖sourceWeightedDiagonalRoot w r hr n hn q-(freeHillValue n:ℂ)-q.val (mode 0)‖ ≤
          2*endpointHillConstant r*(n:ℝ)^(r-1/2)*R^2 ∧
        (q.val (mode 0) = 0 → ‖sourceWeightedDiagonalRoot w r hr n hn q-(freeHillValue n:ℂ)‖ ≤ R/8) := by
  obtain ⟨N, hN, hroot⟩ := source_uniform_diagonal_roots r hr R
  refine ⟨N, hN, fun n hn hnN w q hq => ?_⟩
  obtain ⟨_, ha, hstrip, he, herr, hmean⟩ := hroot n hn hnN (sourceForgetWeight w r q)
    ((norm_sourceForgetWeight_le w r q).trans hq)
  refine ⟨?_, hstrip, he, ?_, ?_⟩
  · exact ha.comp (f := sourceForgetWeight w r) ((sourceForgetWeight w r).analyticAt q)
  · simpa only [sourceWeightedDiagonalRoot, sourceForgetWeight_val] using herr
  · intro hzero
    exact hmean (by simpa only [sourceForgetWeight_val] using hzero)

end NLS.Articles.KdVPseudomeasures
