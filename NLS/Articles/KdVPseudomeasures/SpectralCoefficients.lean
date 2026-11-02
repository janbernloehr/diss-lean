import NLS.Articles.KdVPseudomeasures.SpectralAnalytic
import NLS.KdV.PseudomeasureRootSeparation

/-! # The actual source coefficients and full determinant conclusion of Lemma 2.11

The parameters are original complex endpoint distributions and the original
endpoint norm. The statements below hold on the entire period-two complex
space, hence in particular on the paper's complex mean-zero period-one
subspace and on its real physical source. Root multiplicity here means
analytic order of the actual effective determinant, not an unproved algebraic
multiplicity identification for the physical operator.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The literal entries a_n, b_n and b_-n of the original physical effective matrix. -/
def sourceEndpointEntries (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ)
    (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ) : ℂ × ℂ × ℂ :=
  let e := (sourceEndpointCoefficients r p.1,p.2)
  (NLS.KdV.endpointDiagonal r hr.1 hr.2 n e,
    NLS.KdV.endpointUpperCoupling r hr.1 hr.2 n e,
    NLS.KdV.endpointLowerCoupling r hr.1 hr.2 n e)

/-- The source coefficients are jointly complex analytic in the exact original norm and lambda. -/
theorem analyticAt_sourceEndpointEntries (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ NLS.KdV.reducedHillStrip n)
    (hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (sourceEndpointEntries r hr n) p := by
  let P := (sourceEndpointCoefficientsCLM r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hsE : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖(P p).1‖ ≤ 1/2 := by
    change NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r p.1‖ ≤ 1/2
    rwa [norm_sourceEndpointCoefficients]
  obtain ⟨hA,hB,hC⟩ := NLS.KdV.analyticAt_endpointCoefficients r hr.1 hr.2 n hn (P p) hz hsE
  exact (hA.prod (hB.prod hC)).comp (f := P) (P.analyticAt p)

/-- Lemma 2.9 in the main-theorem unit-weight scale, with original complex
distributions, exact norms and coefficients. The weighted library estimate
`endpointHillCorrectedMode_coefficient_error` retains every spectral weight. -/
theorem sourceLemma2_9_unit (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n)
    (hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    AnalyticAt ℂ (sourceEndpointEntries r hr n) (q,z) ∧
      ‖(sourceEndpointEntries r hr n (q,z)).1-q.val (mode 0)‖ ≤
        2*(NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      (Weight.sobolev r (2*(n:ℤ)))⁻¹*
        ‖(sourceEndpointEntries r hr n (q,z)).2.1-q.val (mode (-(2*(n:ℤ))))‖ ≤
          2*(NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
      (Weight.sobolev r (2*(n:ℤ)))⁻¹*
        ‖(sourceEndpointEntries r hr n (q,z)).2.2-q.val (mode (2*(n:ℤ)))‖ ≤
          2*(NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  have hsE : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rwa [norm_sourceEndpointCoefficients]
  refine ⟨analyticAt_sourceEndpointEntries r hr n hn (q,z) hz hs, ?_, ?_⟩
  · simpa only [sourceEndpointEntries, sourceEndpointCoefficients_apply,
      norm_sourceEndpointCoefficients, neg_zero] using
      NLS.KdV.endpointDiagonal_error_le r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) hsE
  · simpa only [sourceEndpointEntries, sourceEndpointCoefficients_apply,
      norm_sourceEndpointCoefficients, neg_neg] using
      NLS.KdV.endpointCoupling_errors_le r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) hsE

/-- The original source matrix has its literal equal-diagonal determinant formula. -/
theorem sourceEndpointDeterminant_factorization (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (z : ℂ) (hz : z ∈ NLS.KdV.reducedHillStrip n)
    (hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceEndpointDeterminant r hr n (q,z) =
      (z-(NLS.KdV.freeHillValue n:ℂ)-(sourceEndpointEntries r hr n (q,z)).1)^2 -
        (sourceEndpointEntries r hr n (q,z)).2.1*(sourceEndpointEntries r hr n (q,z)).2.2 := by
  have hsE : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rwa [norm_sourceEndpointCoefficients]
  exact NLS.KdV.endpointReducedDeterminant_factorization r hr.1 hr.2 n hn
    (sourceEndpointCoefficients r q) hsE z hz

/-- The source's full-strip supremum of the actual product of its two couplings. -/
def sourceEndpointCouplingRadius (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ℝ :=
  sSup ((fun z : ℂ => Real.sqrt ‖(sourceEndpointEntries r hr n (q,z)).2.1*
    (sourceEndpointEntries r hr n (q,z)).2.2‖) '' NLS.KdV.reducedHillStrip n)

/-- Lemma 2.11, including (23), uniformly on exact original complex endpoint norm balls.
The determinant zeros are counted by analytic order; physical spectral labels are separate. -/
theorem sourceLemma2_11_uniform (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ, N ≤ n →
        NLS.ComplexAnalysis.analyticZeroCount (fun z => sourceEndpointDeterminant r hr n (q,z))
          (Metric.closedBall (NLS.KdV.freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ))) = 2 ∧
        NLS.ComplexAnalysis.analyticZeroCount (fun z => sourceEndpointDeterminant r hr n (q,z))
          (NLS.KdV.reducedHillStrip n) = 2 ∧
        (∀ z ∈ NLS.KdV.reducedHillStrip n, sourceEndpointDeterminant r hr n (q,z) = 0 →
          ‖z-(NLS.KdV.freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4) ∧
        (∀ z ∈ NLS.KdV.reducedHillStrip n, ∀ y ∈ NLS.KdV.reducedHillStrip n,
          sourceEndpointDeterminant r hr n (q,z) = 0 →
          sourceEndpointDeterminant r hr n (q,y) = 0 →
            ‖z-y‖ ≤ Real.sqrt 6 * sourceEndpointCouplingRadius r hr n q) := by
  obtain ⟨N,hN,hcut⟩ := NLS.KdV.exists_endpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hnN
  have hn : 1 ≤ n := hN.trans hnN
  have hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq (mul_nonneg (NLS.KdV.endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  refine ⟨?_,?_,?_,?_⟩
  · exact NLS.KdV.endpointReducedDeterminant_two_zeros r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) hs
  · exact NLS.KdV.endpointReducedDeterminant_strip_two_zeros r hr.1 hr.2 n hn (sourceEndpointCoefficients r q) hs
  · intro z hz hd
    exact NLS.KdV.endpointReducedDeterminant_zero_localization r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q) hs z hz hd
  · intro z hz y hy hdz hdy
    exact NLS.KdV.endpointReduced_roots_separation_sqrt r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q) hs z y hz hy hdz hdy

end NLS.Articles.KdVPseudomeasures
