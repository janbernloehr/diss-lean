import NLS.ZakharovShabat.SpectralPolynomialOrders

/-!
# Exact multiplicities in sufficiently large cutoffs

Disjointness of the central cluster and the counted high discs identifies
the unique factor contributing at each actual spectral value.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every cutoff already has the original multiplicity at each central spectral value. -/
theorem polynomialCutoff_order_of_central (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (M : ℕ) (z : ℂ) (hz : z ∈ centralPeriodicSpectrum hp (weightedBaseToPair w φ) N) :
    analyticOrderAt (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M) z =
      (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  rw [analyticOrderAt_periodicSpectralPolynomialCutoff, analyticOrderAt_centralPeriodicPolynomial, if_pos hz]
  have hs : (∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
      analyticOrderAt (fun t => spectralPairFactor ξ η t n) z) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : N < n.natAbs := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
      omega
    exact (hr n hn').factor_order_zero ξ η z
      (Finset.disjoint_left.mp (hc.central_disjoint_disk n hn') hz)
  rw [hs, add_zero]

/-- A high spectral value has its original multiplicity once the cutoff includes its disc. -/
theorem polynomialCutoff_order_of_disk (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (n : ℤ) (hn : N < n.natAbs) (M : ℕ) (hM : n.natAbs ≤ M) (z : ℂ)
    (hz : z ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4)) :
    analyticOrderAt (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M) z =
      (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  have hzc : z ∉ centralPeriodicSpectrum hp (weightedBaseToPair w φ) N :=
    fun h => Finset.disjoint_left.mp (hc.central_disjoint_disk n hn) h hz
  rw [analyticOrderAt_periodicSpectralPolynomialCutoff, analyticOrderAt_centralPeriodicPolynomial, if_neg hzc, zero_add]
  rw [Finset.sum_eq_single n]
  · exact (hr n hn).factor_order ξ η z hz
  · intro m hm hmn
    have hm' : N < m.natAbs := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at hm
      omega
    apply (hr m hm').factor_order_zero ξ η z
    intro hzm
    exact (periodicDisks_disjoint m n hmn).le_bot
      ⟨((mem_enclosedPeriodicSpectrum hp _ _ z _).mp hzm).2,
        ((mem_enclosedPeriodicSpectrum hp _ _ z _).mp hz).2⟩
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · constructor <;> omega
    · omega

/-- For every spectral parameter, all sufficiently large cutoffs have exactly its original multiplicity. -/
theorem eventually_polynomialCutoff_order_eq_multiplicity (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ) :
    ∀ᶠ M : ℕ in atTop,
      analyticOrderAt (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M) z =
        (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  by_cases hz : z ∈ periodicSpectrum hp (weightedBaseToPair w φ)
  · rcases (hc.mem_spectrum_iff_central_or_disk z).mp hz with hz | ⟨n,hn,_⟩
    · exact Filter.Eventually.of_forall (fun M => polynomialCutoff_order_of_central hp w φ N ξ η hc hr M z hz)
    · filter_upwards [eventually_ge_atTop n.natAbs] with M hM
      exact polynomialCutoff_order_of_disk hp w φ N ξ η hc hr n hn.1 M hM z hn.2
  · apply Filter.Eventually.of_forall
    intro M
    have hres : z ∈ resolventSet hp (weightedBaseToPair w φ) := by
      simpa only [periodicSpectrum, Set.mem_compl_iff, not_not] using hz
    rw [(periodicAlgebraicMultiplicity_eq_zero_iff hp _ z).mpr hres, Nat.cast_zero]
    exact analyticOrderAt_eq_zero.mpr (Or.inr (periodicSpectralPolynomialCutoff_ne_zero hp w φ N ξ η hr M z hz))

end NLS.ZakharovShabat
