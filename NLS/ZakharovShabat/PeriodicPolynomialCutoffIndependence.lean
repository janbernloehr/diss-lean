import NLS.ZakharovShabat.CentralSpectrumCutoffs
import NLS.ZakharovShabat.PeriodicSpectralProductsUniform

/-!
# Central-cutoff independence of finite spectral polynomials

Absorbing a counted pair into the central polynomial preserves its full
multiplicity, including a double root. The corresponding constant normalization
moves with it. The resulting identities hold even at spectral zeros.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Nested symmetric integer cutoffs are nested finite sets. -/
theorem spectralIndexInterval_mono {N K : ℕ} (hNK : N ≤ K) :
    Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  intro n hn
  simp only [Finset.mem_Icc] at hn ⊢
  constructor <;> omega

/-- Split an annular product at any intermediate central cutoff. -/
theorem prod_spectralIndexAnnulus (f : ℤ → ℂ) {N K M : ℕ} (hNK : N ≤ K) (hKM : K ≤ M) :
    (∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), f n) =
      (∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), f n) *
      ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(K : ℤ)) (K : ℤ), f n := by
  have he : Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ) =
      (Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)) ∪
      (Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [he, Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro n hn hm
  exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_sdiff.mp hn).1

/-- Enlarging the central normalization includes exactly the intervening denominators. -/
theorem centralSpectralNormalization_eq_mul {N K : ℕ} (hNK : N ≤ K) :
    centralSpectralNormalization K = centralSpectralNormalization N *
      ∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
        spectralPairDenominator n := by
  unfold centralSpectralNormalization
  rw [← Finset.prod_sdiff (spectralIndexInterval_mono hNK), mul_comm]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A disc's finite root polynomial is the two-root factor even when both roots coincide. -/
theorem PeriodicResonantPair.rootPolynomial {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {x y : ℂ}
    (h : PeriodicResonantPair hp w φ n x y) (z : ℂ) :
    (∏ a ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4),
      (a-z) ^ periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) a) = (x-z)*(y-z) := by
  classical
  have hx := h.multiplicity_eq_count x (refinedResonantDisk_subset_strip n h.left_mem)
  have hy := h.multiplicity_eq_count y (refinedResonantDisk_subset_strip n h.right_mem)
  rw [h.enclosed_eq]
  by_cases he : x = y
  · subst y
    simp at hx
    simp [hx, pow_two]
  · rw [Finset.prod_pair he, hx, hy]
    simp [he, Ne.symm he]

/-- The larger central polynomial absorbs precisely the intervening actual pairs. -/
theorem centralPeriodicPolynomial_eq_mul (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N K : ℕ) (hNK : N ≤ K) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ) :
    centralPeriodicPolynomial hp (weightedBaseToPair w φ) K z =
      centralPeriodicPolynomial hp (weightedBaseToPair w φ) N z *
      ∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (ξ n-z)*(η n-z) := by
  classical
  unfold centralPeriodicPolynomial
  rw [hc.centralSpectrum_eq_union K hNK, Finset.prod_union (hc.central_disjoint_addedDisks K)]
  congr 1
  rw [Finset.prod_biUnion (fun n _ m _ hnm => enclosedPeriodicSpectrum_disjoint hp _ n m hnm)]
  apply Finset.prod_congr rfl
  intro n hn
  have hn' : N < n.natAbs := by
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  exact (hr n hn').rootPolynomial z

/-- Once the outer cutoff contains both central clusters, the entire polynomials agree exactly. -/
theorem periodicSpectralPolynomialCutoff_eq_of_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N K M : ℕ) (hNK : N ≤ K) (hKM : K ≤ M)
    (ξ η : ℤ → ℂ) (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M =
      periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) K ξ η M := by
  funext z
  unfold periodicSpectralPolynomialCutoff
  rw [centralPeriodicPolynomial_eq_mul hp w φ N K hNK ξ η hc hr z,
    centralSpectralNormalization_eq_mul hNK, prod_spectralIndexAnnulus _ hNK hKM]
  have he : (∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralPairFactor ξ η z n) =
      (∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), (ξ n-z)*(η n-z)) /
      ∏ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairDenominator n := by
    simp only [spectralPairFactor_eq_div, Finset.prod_div_distrib]
  rw [he]
  ring

end NLS.ZakharovShabat
