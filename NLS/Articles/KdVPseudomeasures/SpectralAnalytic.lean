import NLS.Articles.KdVPseudomeasures.SpectralReduction
import NLS.KdV.PseudomeasureAnalytic
import NLS.KdV.PseudomeasureZeroCount

/-! # Analytic determinant on the original pseudomeasure source space

The complex Banach parameter is the actual original distribution, with its
exact endpoint norm. Restricting to physical real mean-zero period-one
potentials preserves the previously proved physical eigenvector criterion.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The already identified exact source coefficients form a bounded linear map. -/
def sourceEndpointCoefficientsCLM (r : ℝ) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  LinearMap.mkContinuous
    { toFun := sourceEndpointCoefficients r
      map_add' := by intros; apply Subtype.ext; rfl
      map_smul' := by intros; apply Subtype.ext; rfl }
    1 (fun q => by
      change ‖sourceEndpointCoefficients r q‖ ≤ 1*‖q‖
      rw [norm_sourceEndpointCoefficients, one_mul])

@[simp] theorem sourceEndpointCoefficientsCLM_apply (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceEndpointCoefficientsCLM r q = sourceEndpointCoefficients r q := rfl

/-- The actual endpoint determinant with original-distribution parameters. -/
def sourceEndpointDeterminant (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ)
    (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ) : ℂ :=
  NLS.KdV.endpointReducedDeterminant r hr.1 hr.2 n (sourceEndpointCoefficients r p.1,p.2)

/-- Joint complex Banach analyticity in the original source norm and lambda.
Closed-strip boundary points and zeros of the determinant are included. -/
theorem analyticAt_sourceEndpointDeterminant (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ NLS.KdV.reducedHillStrip n)
    (hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (sourceEndpointDeterminant r hr n) p := by
  let P := (sourceEndpointCoefficientsCLM r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hsE : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖(P p).1‖ ≤ 1/2 := by
    change NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r p.1‖ ≤ 1/2
    rwa [norm_sourceEndpointCoefficients]
  change AnalyticAt ℂ (NLS.KdV.endpointReducedDeterminant r hr.1 hr.2 n ∘ P) p
  exact (NLS.KdV.analyticAt_endpointReducedDeterminant r hr.1 hr.2 n hn (P p) hz hsE).comp
    (P.analyticAt p)

/-- The analytic function detects precisely the original physical Hill eigen-equation. -/
theorem sourceEndpointDeterminant_eq_zero_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : Potential r) (z : ℂ)
    (hz : z ∈ NLS.KdV.reducedHillStrip n)
    (hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    sourceEndpointDeterminant r hr n (q.val,z) = 0 ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        NLS.KdV.singularHillOperator (potentialHminusOne r hr q) f =
          z • NLS.KdV.singularHillDomainInclusion f := by
  have hsE : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q.val‖ ≤ 1/2 := by
    rwa [norm_sourceEndpointCoefficients]
  have h := NLS.KdV.endpointReducedDeterminant_eq_zero_iff r hr.1 hr.2 n hn
    (sourceEndpointCoefficients r q.val,z) hz hsE
  simpa only [sourceEndpointDeterminant, sourceEndpointCoefficients_HminusOne r hr q] using h

/-- The cutoff is chosen before q, n and lambda on every exact original
source norm ball. No analyticity or invertibility premise is supplied by a caller. -/
theorem source_uniform_analytic_physical_reduction (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∀ (n : ℕ) (_hn : 1 ≤ n), N ≤ n → ∀ (z : ℂ) (_hz : z ∈ NLS.KdV.reducedHillStrip n),
        AnalyticAt ℂ (sourceEndpointDeterminant r hr n) (q.val,z) ∧
          (sourceEndpointDeterminant r hr n (q.val,z) = 0 ↔
            ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
              NLS.KdV.singularHillOperator (potentialHminusOne r hr q) f =
                z • NLS.KdV.singularHillDomainInclusion f) := by
  obtain ⟨N,hN,hcut⟩ := NLS.KdV.exists_endpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hnN z hz
  have hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (NLS.KdV.endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  exact ⟨analyticAt_sourceEndpointDeterminant r hr n hn (q.val,z) hz hs,
    sourceEndpointDeterminant_eq_zero_iff r hr n hn q z hz hs⟩

/-- The zero-count and localization conclusions of Lemma 2.11, uniformly
on exact original source norm balls. The root-separation estimate (23)
and equality with operator algebraic multiplicities are separate results. -/
theorem sourceLemma2_11_uniform_zero_count (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∀ (n : ℕ) (_hn : 1 ≤ n), N ≤ n →
        NLS.ComplexAnalysis.analyticZeroCount (fun z => sourceEndpointDeterminant r hr n (q.val,z))
          (Metric.closedBall (NLS.KdV.freeHillValue n:ℂ) (4*Real.sqrt (n:ℝ))) = 2 ∧
        NLS.ComplexAnalysis.analyticZeroCount (fun z => sourceEndpointDeterminant r hr n (q.val,z))
          (NLS.KdV.reducedHillStrip n) = 2 ∧
        ∀ z ∈ NLS.KdV.reducedHillStrip n, sourceEndpointDeterminant r hr n (q.val,z) = 0 →
          ‖z-(NLS.KdV.freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  obtain ⟨N,hN,hcut⟩ := NLS.KdV.exists_endpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hnN
  have hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q.val‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq (mul_nonneg (NLS.KdV.endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  refine ⟨?_,?_,?_⟩
  · simpa only [sourceEndpointDeterminant] using
      NLS.KdV.endpointReducedDeterminant_two_zeros r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val) hs
  · simpa only [sourceEndpointDeterminant] using
      NLS.KdV.endpointReducedDeterminant_strip_two_zeros r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val) hs
  · intro z hz hd
    exact NLS.KdV.endpointReducedDeterminant_zero_localization r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q.val) hs z hz hd

end NLS.Articles.KdVPseudomeasures
