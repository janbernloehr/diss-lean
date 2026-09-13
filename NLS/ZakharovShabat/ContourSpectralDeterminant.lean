import NLS.ZakharovShabat.ContourReductionMultiplicity
import NLS.FunctionalAnalysis.FiniteSpectralDeterminant

/-!
# Intrinsic analytic contour determinants

The determinant on a varying spectral range equals its transported determinant
on a fixed finite-dimensional space. It is jointly analytic in the spectral
parameter and potential, and equals the actual finite spectral product with
original algebraic multiplicities.
-/

noncomputable section
open Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral determinant on the actual contour range, with the `(L-z)` orientation. -/
def contourSpectralDeterminant (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ((reducedContourOperator hp φ φ c r).toLinearMap-z • 1).det

/-- Projection transport preserves the complete determinant and its normalization. -/
theorem contourSpectralDeterminant_eq_reduced (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hφ : sphere c r ⊆ resolventSet hp φ)
    (hψ : sphere c r ⊆ resolventSet hp ψ) (hu : IsUnit (contourTransport hp φ ψ c r)) (z : ℂ) :
    contourSpectralDeterminant hp ψ c r z =
      ((reducedContourOperator hp φ ψ c r).toLinearMap-z • 1).det := by
  let e := ProjectionTransport.rangeEquivalence _ _
    (resolventCircleIntegral_idempotent hp φ c r hr hφ)
    (resolventCircleIntegral_idempotent hp ψ c r hr hψ) hu
  have he := reducedContourOperator_conjugate hp φ ψ c r hr hφ hψ hu
  change e.toLinearEquiv.conjAlgEquiv ℂ (reducedContourOperator hp φ ψ c r).toLinearMap = _ at he
  unfold contourSpectralDeterminant
  rw [← he]
  exact FiniteSpectralDeterminant.shifted_det_conj e.toLinearEquiv _ z

/-- Intrinsic spectral determinants are jointly analytic wherever their contour is in the resolvent. -/
theorem analyticAt_contourSpectralDeterminant (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × PairSpace p => contourSpectralDeterminant hp t.2 c r t.1) (z,φ) := by
  let : FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  obtain ⟨U,ho,hφ,_,_,hA,hU⟩ := exists_local_contourReduction hp φ c r hr hc
  have ha := FiniteSpectralDeterminant.analyticAt_shifted_det
    ((hA φ hφ).comp (analyticAt_snd (p := (z,φ)))) (analyticAt_fst (p := (z,φ)))
  apply ha.congr
  filter_upwards [(continuous_snd.tendsto (z,φ)) (ho.mem_nhds hφ)] with t ht
  exact (contourSpectralDeterminant_eq_reduced hp φ t.2 c r hr hc (hU t.2 ht).1
    (hU t.2 ht).2.1 t.1).symm

/-- The determinant is the actual root product with original generalized-root-space multiplicities. -/
theorem contourSpectralDeterminant_eq_prod (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (z : ℂ) :
    contourSpectralDeterminant hp φ c r z =
      ∏ a ∈ enclosedPeriodicSpectrum hp φ c r, (a-z)^periodicAlgebraicMultiplicity hp φ a := by
  classical
  let : FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  let A : Module.End ℂ (resolventCircleIntegral hp φ c r).range :=
    (reducedContourOperator hp φ φ c r).toLinearMap
  have he : A.charpoly.roots.toFinset = enclosedPeriodicSpectrum hp φ c r := by
    ext a
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact reducedContourOperator_hasEigenvalue_iff hp φ c a r hr hc
  change (A-z • 1).det = _
  rw [FiniteSpectralDeterminant.shifted_det_eq_prod_roots, he]
  apply Finset.prod_congr rfl
  intro a ha
  rw [reducedContourOperator_rootMultiplicity hp φ c a r hr hc
    ((mem_enclosedPeriodicSpectrum hp φ c a r).mp ha).2]

/-- The finite actual spectral product is jointly analytic; individual roots need not be analytic. -/
theorem analyticAt_enclosedPeriodicPolynomial (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × PairSpace p =>
      ∏ a ∈ enclosedPeriodicSpectrum hp t.2 c r, (a-t.1)^periodicAlgebraicMultiplicity hp t.2 a) (z,φ) := by
  apply (analyticAt_contourSpectralDeterminant hp φ c r hr hc z).congr
  filter_upwards [(continuous_snd.tendsto (z,φ)) ((isOpen_resolventCircleDomain hp c r).mem_nhds hc)] with t ht
  exact contourSpectralDeterminant_eq_prod hp t.2 c r hr ht t.1

end NLS.ZakharovShabat
