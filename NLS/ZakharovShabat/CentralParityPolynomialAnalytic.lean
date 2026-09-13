import NLS.ZakharovShabat.ParityContourMultiplicity
import NLS.ZakharovShabat.ParityLiteralCutoffs
import NLS.ZakharovShabat.CentralPolynomialAnalytic

/-!
# Joint analyticity of the intrinsic central parity polynomials

On the even-supported potential subspace, each central parity polynomial is
the determinant of the original parity contour reduction. The corrected
normalizations give analytic finite approximants for the two parity products.
-/

noncomputable section
open Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual central parity polynomial equals its original contour determinant. -/
theorem centralParityPolynomial_eq_contourDeterminant (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (r : ℤ)
    (hc : sphere 0 (centralCircleRadius N) ⊆ resolventSet hp φ)
    (he : enclosedPeriodicSpectrum hp φ 0 (centralCircleRadius N) = centralPeriodicSpectrum hp φ N)
    (z : ℂ) :
    centralParityPolynomial hp φ N r z = parityContourDeterminant hp φ 0 (centralCircleRadius N) r z := by
  rw [parityContourDeterminant_eq_prod hp φ hφ 0 _ r (centralCircleRadius_pos N).le hc z, he]
  rfl

/-- All sufficiently large central parity polynomials are jointly analytic on a common actual neighborhood. -/
theorem exists_uniform_analytic_centralParityPolynomials (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N ≥ N₀, ∀ r : ℤ, AnalyticOnNhd ℂ
        (fun t : ℂ × pairParitySubspace (p := p) 0 => centralParityPolynomial hp t.2 N r t.1)
        {t | (t.2 : PairSpace p) ∈ U} := by
  obtain ⟨N₀,U,hN₀,ho,hconv,hφ,h0,hU⟩ := exists_uniform_centralCircle hp φ
  refine ⟨N₀,U,hN₀,ho,hconv,hφ,h0,?_⟩
  intro N hN r t ht
  have hsub : Continuous (fun a : ℂ × pairParitySubspace (p := p) 0 => (a.2 : PairSpace p)) :=
    continuous_subtype_val.comp continuous_snd
  apply (analyticAt_parityContourDeterminant hp t.2 0 _ r (centralCircleRadius_pos N).le
    (hU t.2 ht N hN).2.1 t.1).congr
  filter_upwards [(hsub.tendsto t) (ho.mem_nhds ht)] with a ha
  exact (centralParityPolynomial_eq_contourDeterminant hp a.2 a.2.property N r
    (hU a.2 ha N hN).2.1 (hU a.2 ha N hN).2.2.1 a.1).symm

/-- Intrinsic normalized parity approximants with the necessary prefactors `-1` and `4`. -/
def normalizedCentralParityPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) (z : ℂ) : ℂ :=
  (if r % 2 = 0 then (-1 : ℂ) else 4) * centralParityPolynomial hp φ N r z / centralParityNormalization N r

/-- Each normalized parity approximant is entire in the spectral parameter. -/
theorem analyticOnNhd_normalizedCentralParityPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) :
    AnalyticOnNhd ℂ (normalizedCentralParityPolynomial hp φ N r) Set.univ := by
  intro z hz
  exact (analyticAt_const.mul (analyticOnNhd_centralParityPolynomial hp φ N r z hz)).div_const

/-- The intrinsic normalized parity approximants are jointly analytic on one common neighborhood. -/
theorem exists_uniform_analytic_normalizedCentralParityPolynomials (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N ≥ N₀, ∀ r : ℤ, AnalyticOnNhd ℂ
        (fun t : ℂ × pairParitySubspace (p := p) 0 => normalizedCentralParityPolynomial hp t.2 N r t.1)
        {t | (t.2 : PairSpace p) ∈ U} := by
  obtain ⟨N₀,U,hN₀,ho,hconv,hφ,h0,h⟩ := exists_uniform_analytic_centralParityPolynomials hp φ
  refine ⟨N₀,U,hN₀,ho,hconv,hφ,h0,?_⟩
  intro N hN r t ht
  exact (analyticAt_const.mul (h N hN r t ht)).div_const

/-- The analytic intrinsic approximants recover the literal actual cutoffs, retaining the odd boundary pair. -/
theorem CompletePeriodicParityPairs.cutoffs_eq_normalizedParity {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (hM : N ≤ 2*M) (z : ℂ) :
    evenSpectralPairCutoff ξ η z M = normalizedCentralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 0 z ∧
    oddSpectralPairCutoff ξ η z M = normalizedCentralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 1 z *
      spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  constructor
  · simpa [normalizedCentralParityPolynomial] using h.evenCutoff_eq_central M hM z
  · simpa [normalizedCentralParityPolynomial] using h.oddCutoff_eq_central M hM z

end NLS.ZakharovShabat
