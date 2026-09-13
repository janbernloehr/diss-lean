import NLS.ZakharovShabat.EntirePeriodicProductZeros
import NLS.ComplexAnalysis.FiniteProductOrders

/-!
# Orders of the actual finite spectral polynomials

The finite central exponents are original spectral algebraic multiplicities.
Each distant counted pair contributes its multiset count, including double roots.
Nonzero constant normalizations do not alter orders.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual central polynomial has precisely its prescribed original multiplicities. -/
theorem analyticOrderAt_centralPeriodicPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    analyticOrderAt (centralPeriodicPolynomial hp φ N) z =
      if z ∈ centralPeriodicSpectrum hp φ N then (periodicAlgebraicMultiplicity hp φ z : ℕ∞) else 0 :=
  NLS.ComplexAnalysis.analyticOrderAt_rootPolynomial _ _ z

/-- An original normalized two-root factor counts both entries, even when they coincide. -/
theorem analyticOrderAt_spectralPairFactor (ξ η : ℤ → ℂ) (n : ℤ) (z : ℂ) :
    analyticOrderAt (fun t => spectralPairFactor ξ η t n) z =
      (({ξ n,η n} : Multiset ℂ).count z : ℕ∞) := by
  classical
  simp_rw [spectralPairFactor_eq_div]
  rw [NLS.ComplexAnalysis.analyticOrderAt_div_const _ z _ (spectralPairDenominator_ne_zero n) (by fun_prop)]
  change analyticOrderAt ((fun t => ξ n-t)*(fun t => η n-t)) z = _
  rw [analyticOrderAt_mul (by fun_prop) (by fun_prop),
    NLS.ComplexAnalysis.analyticOrderAt_const_sub, NLS.ComplexAnalysis.analyticOrderAt_const_sub]
  simp [Multiset.count_cons, Multiset.count_singleton, eq_comm, add_comm]

/-- The whole finite cutoff's order splits into the central order and the distant pair orders. -/
theorem analyticOrderAt_periodicSpectralPolynomialCutoff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (M : ℕ) (z : ℂ) :
    analyticOrderAt (periodicSpectralPolynomialCutoff hp φ N ξ η M) z =
      analyticOrderAt (centralPeriodicPolynomial hp φ N) z +
        ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
          analyticOrderAt (fun t => spectralPairFactor ξ η t n) z := by
  have hcp : AnalyticAt ℂ (centralPeriodicPolynomial hp φ N) z := by
    unfold centralPeriodicPolynomial
    fun_prop
  have hcoef : analyticOrderAt (fun t => -4*centralPeriodicPolynomial hp φ N t / centralSpectralNormalization N) z =
      analyticOrderAt (centralPeriodicPolynomial hp φ N) z := by
    rw [NLS.ComplexAnalysis.analyticOrderAt_div_const _ z _ (centralSpectralNormalization_ne_zero N) (by fun_prop)]
    change analyticOrderAt ((fun _ : ℂ => (-4 : ℂ)) * centralPeriodicPolynomial hp φ N) z = _
    have hconst : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
    rw [analyticOrderAt_mul analyticAt_const hcp, hconst, zero_add]
  have ht : AnalyticAt ℂ (fun t => ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralPairFactor ξ η t n) z := Finset.analyticAt_fun_prod _
    (fun n _ => analyticOnNhd_spectralPairFactor ξ η n Set.univ z (Set.mem_univ z))
  change analyticOrderAt ((fun t => -4*centralPeriodicPolynomial hp φ N t / centralSpectralNormalization N) *
    (fun t => ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η t n)) z = _
  rw [analyticOrderAt_mul (by fun_prop) ht, hcoef,
    NLS.ComplexAnalysis.analyticOrderAt_finsetProd _ _ z
      (fun n _ => analyticOnNhd_spectralPairFactor ξ η n Set.univ z (Set.mem_univ z))]

/-- In its counted disc, a pair factor's order is the original algebraic multiplicity. -/
theorem PeriodicResonantPair.factor_order {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} (ξ η : ℤ → ℂ)
    (h : PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ)
    (hz : z ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4)) :
    analyticOrderAt (fun t => spectralPairFactor ξ η t n) z =
      (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  have hroot := hz
  rw [h.enclosed_eq] at hroot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hroot
  have hstrip : z ∈ resonantStrip n := by
    rcases hroot with rfl | rfl
    · exact refinedResonantDisk_subset_strip n h.left_mem
    · exact refinedResonantDisk_subset_strip n h.right_mem
  rw [analyticOrderAt_spectralPairFactor, ← h.multiplicity_eq_count z hstrip]

/-- A counted pair contributes no order outside its actual spectral disc. -/
theorem PeriodicResonantPair.factor_order_zero {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} (ξ η : ℤ → ℂ)
    (h : PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ)
    (hz : z ∉ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4)) :
    analyticOrderAt (fun t => spectralPairFactor ξ η t n) z = 0 := by
  classical
  rw [h.enclosed_eq] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  rw [analyticOrderAt_spectralPairFactor]
  simp [hz.1, hz.2]

end NLS.ZakharovShabat
