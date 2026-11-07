import NLS.Articles.KdVPseudomeasures.SpectralComplexGaps
import NLS.KdV.PseudomeasureWeightedGaps

/-!
# The original weighted complex distributions and the same physical spectral coefficients

The source explicitly uses period-two Fourier modes even for physical
period-one potentials. Both the norm and every smooth-test action are retained.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Exact original weighted source coefficients, with no frequency renormalization. -/
def sourceWeightedEndpointCoefficients (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    WeightedCoeff (w.negativeSobolev r) ⊤ :=
  coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r) q

@[simp] theorem sourceWeightedEndpointCoefficients_apply (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (k : ℤ) :
    (sourceWeightedEndpointCoefficients w r q).val k = q.val (mode (-k)) := rfl

theorem norm_sourceWeightedEndpointCoefficients (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    ‖sourceWeightedEndpointCoefficients w r q‖ = ‖q‖ :=
  (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).norm_map q

/-- Forget only the extra weight in the ORIGINAL distribution norm. -/
def sourceForgetWeight (w : SpectralWeight) (r : ℝ) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-r) ⊤ :=
  (sobolevCoefficients (-r) ⊤).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((w.negativeSobolevToSobolev r ⊤).comp
      (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Every original smooth-test action, hence all physical source constraints, is unchanged. -/
theorem sourceForgetWeight_val (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    (sourceForgetWeight w r q).val = q.val := by
  apply Distribution.ext_coefficients
  intro k
  change ((sobolevCoefficients (-r) ⊤) ((sobolevCoefficients (-r) ⊤).symm
    (w.negativeSobolevToSobolev r ⊤ (sourceWeightedEndpointCoefficients w r q)))).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply, SpectralWeight.negativeSobolevToSobolev_apply,
    sourceWeightedEndpointCoefficients_apply]

/-- The exact original weighted norm controls the identical original unweighted norm with constant1. -/
theorem norm_sourceForgetWeight_le (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    ‖sourceForgetWeight w r q‖ ≤ ‖q‖ := by
  change ‖(sobolevCoefficients (-r) ⊤).symm
    (w.negativeSobolevToSobolev r ⊤ (sourceWeightedEndpointCoefficients w r q))‖ ≤ ‖q‖
  rw [LinearIsometryEquiv.norm_map]
  exact (w.norm_negativeSobolevToSobolev_le r ⊤ _).trans_eq
    (norm_sourceWeightedEndpointCoefficients w r q)

/-- The original-distribution adapter and native coefficient inclusion agree exactly. -/
theorem sourceEndpointCoefficients_forgetWeight (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    sourceEndpointCoefficients r (sourceForgetWeight w r q) =
      endpointForgetWeight w r (sourceWeightedEndpointCoefficients w r q) := by
  apply Subtype.ext
  funext k
  rw [sourceEndpointCoefficients_apply, sourceForgetWeight_val,
    endpointForgetWeight_apply, sourceWeightedEndpointCoefficients_apply]

/-- The original physical H-minus-one potential is the same weighted source distribution. -/
theorem sourceComplexHminusOne_forgetWeight (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    sourceComplexHminusOne r hr (sourceForgetWeight w r q) =
      endpointHillHminusOne w r hr.2 (sourceWeightedEndpointCoefficients w r q) := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr (sourceForgetWeight w r q),
    sourceEndpointCoefficients_forgetWeight]
  exact endpointHillHminusOne_weightInclusion _ _ _ _ _ _

/-- Lemma2.9 weighted errors for the literal ORIGINAL physical entries and source Fourier coefficients. -/
theorem sourceLemma2_9_weighted_errors (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    w.negativeSobolev r 0*‖(sourceEndpointEntries r hr n (sourceForgetWeight w r q,z)).1-q.val (mode 0)‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖(sourceEndpointEntries r hr n (sourceForgetWeight w r q,z)).2.1-q.val (mode (-(2*(n:ℤ))))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      w.negativeSobolev r (2*(n:ℤ))*‖(sourceEndpointEntries r hr n (sourceForgetWeight w r q,z)).2.2-q.val (mode (2*(n:ℤ)))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  have he := endpointCoefficients_weighted_errors_le w r hr.1 hr.2 n hn z hz
    (sourceWeightedEndpointCoefficients w r q) (by simpa only [norm_sourceWeightedEndpointCoefficients] using hs)
  simpa only [sourceEndpointEntries, sourceEndpointCoefficients_forgetWeight,
    sourceWeightedEndpointCoefficients_apply, norm_sourceWeightedEndpointCoefficients, neg_zero, neg_neg] using he

/-- The same literal entries are jointly analytic in the EXACT original weighted norm and parameter. -/
theorem analyticAt_sourceWeightedEndpointEntries (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    AnalyticAt ℂ (fun p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ × ℂ =>
      sourceEndpointEntries r hr n (sourceForgetWeight w r p.1,p.2)) (q,z) := by
  let P := (sourceForgetWeight w r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs
  exact (analyticAt_sourceEndpointEntries r hr n hn (P (q,z)) hz hsmall).comp
    (f := P) (P.analyticAt (q,z))

end NLS.Articles.KdVPseudomeasures
