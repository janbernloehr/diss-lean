import NLS.ZakharovShabat.ContourSpectralDeterminant
import NLS.ZakharovShabat.PeriodicPolynomialCutoffIndependence

/-!
# Joint analyticity of the actual central polynomials

Large admissible circles enclose exactly the central spectral cluster. Its
original root polynomial is therefore an analytic contour determinant. The
normalization defines intrinsic finite approximants without eigenvalue labels.
-/

noncomputable section
open Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Whenever the central cluster is enclosed by an admissible circle, its polynomial is the determinant. -/
theorem centralPeriodicPolynomial_eq_contourDeterminant (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (hc : sphere 0 (centralCircleRadius N) ⊆ resolventSet hp φ)
    (he : enclosedPeriodicSpectrum hp φ 0 (centralCircleRadius N) = centralPeriodicSpectrum hp φ N)
    (z : ℂ) :
    centralPeriodicPolynomial hp φ N z = contourSpectralDeterminant hp φ 0 (centralCircleRadius N) z := by
  rw [contourSpectralDeterminant_eq_prod hp φ 0 _ (centralCircleRadius_pos N).le hc z, he]
  rfl

/-- All sufficiently large central polynomials are jointly analytic on one potential neighborhood. -/
theorem exists_uniform_analytic_centralPeriodicPolynomials (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N ≥ N₀, AnalyticOnNhd ℂ (fun t : ℂ × PairSpace p => centralPeriodicPolynomial hp t.2 N t.1)
        (Set.univ ×ˢ U) := by
  obtain ⟨N₀,U,hN₀,ho,hconv,hφ,h0,hU⟩ := exists_uniform_centralCircle hp φ
  refine ⟨N₀,U,hN₀,ho,hconv,hφ,h0,?_⟩
  intro N hN t ht
  apply (analyticAt_contourSpectralDeterminant hp t.2 0 _ (centralCircleRadius_pos N).le
    (hU t.2 ht.2 N hN).2.1 t.1).congr
  filter_upwards [(continuous_snd.tendsto t) (ho.mem_nhds ht.2)] with a ha
  exact (centralPeriodicPolynomial_eq_contourDeterminant hp a.2 N
    (hU a.2 ha N hN).2.1 (hU a.2 ha N hN).2.2.1 a.1).symm

/-- Intrinsic normalized finite approximants, using the actual central spectrum alone. -/
def normalizedCentralPeriodicPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) : ℂ :=
  -4 * centralPeriodicPolynomial hp φ N z / centralSpectralNormalization N

/-- Every intrinsic approximant is entire in the spectral parameter, without localization hypotheses. -/
theorem analyticOnNhd_normalizedCentralPeriodicPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    AnalyticOnNhd ℂ (normalizedCentralPeriodicPolynomial hp φ N) Set.univ := by
  intro z _
  unfold normalizedCentralPeriodicPolynomial centralPeriodicPolynomial
  fun_prop

/-- The intrinsic polynomial is exactly the original cutoff when its whole spectrum is central. -/
theorem periodicSpectralPolynomialCutoff_self (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (ξ η : ℤ → ℂ) :
    periodicSpectralPolynomialCutoff hp φ N ξ η N = normalizedCentralPeriodicPolynomial hp φ N := by
  funext z
  simp [periodicSpectralPolynomialCutoff, normalizedCentralPeriodicPolynomial]

/-- Every sufficiently large original cutoff equals the intrinsic normalized polynomial. -/
theorem periodicSpectralPolynomialCutoff_eq_normalizedCentral (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N M : ℕ) (hNM : N ≤ M) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M =
      normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w φ) M := by
  rw [periodicSpectralPolynomialCutoff_eq_of_le hp w φ N M M hNM le_rfl ξ η hc hr,
    periodicSpectralPolynomialCutoff_self]

/-- The intrinsic normalized approximants are jointly analytic for every sufficiently large index. -/
theorem exists_uniform_analytic_normalizedCentralPolynomials (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N ≥ N₀, AnalyticOnNhd ℂ
        (fun t : ℂ × PairSpace p => normalizedCentralPeriodicPolynomial hp t.2 N t.1) (Set.univ ×ˢ U) := by
  obtain ⟨N₀,U,hN₀,ho,hconv,hφ,h0,h⟩ := exists_uniform_analytic_centralPeriodicPolynomials hp φ
  refine ⟨N₀,U,hN₀,ho,hconv,hφ,h0,?_⟩
  intro N hN t ht
  exact (analyticAt_const.mul (h N hN t ht)).div_const

end NLS.ZakharovShabat
