import NLS.ZakharovShabat.CompleteParitySpectrum
import NLS.ZakharovShabat.PeriodicPolynomialCutoffIndependence

/-!
# Growth of actual central parity polynomials

Enlarging the center absorbs exactly the distant pairs in the selected parity.
The opposite parity contributes one. Complete root labels therefore recover
the intrinsic central parity polynomial at every larger cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The central index sets of either parity increase with the cutoff. -/
theorem centralParityIndices_mono {N K : ℕ} (hNK : N ≤ K) (r : ℤ) :
    centralParityIndices N r ⊆ centralParityIndices K r :=
  Finset.filter_subset_filter _ (spectralIndexInterval_mono hNK)

/-- The parity part of an annulus is the difference of the parity index sets. -/
theorem centralParityIndices_sdiff (N K : ℕ) (r : ℤ) :
    centralParityIndices K r \ centralParityIndices N r =
      (Finset.Icc (-(K : ℤ)) K \ Finset.Icc (-(N : ℤ)) N).filter (fun n => n % 2 = r % 2) := by
  ext n
  simp only [centralParityIndices, Finset.mem_sdiff, Finset.mem_filter]
  tauto

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A counted distant disc contributes its two-root polynomial exactly in its index parity. -/
theorem CompletePeriodicParityPairs.distant_parityPolynomial {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (n : ℤ) (hn : N < n.natAbs) (r : ℤ) (z : ℂ) :
    (∏ a ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4),
      (a-z)^parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) r a) =
      if n % 2 = r % 2 then (ξ n-z)*(η n-z) else 1 := by
  classical
  have hs (a : ℂ) (ha : a ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ)
      ((Real.pi : ℂ)*n) (Real.pi/4)) :
      periodicRootSpaceTop hp (weightedBaseToPair w φ) a ≤ pairParitySubspace n :=
    h.counting.disk_rootSpace_parity h.even_potential n hn a
      ((mem_enclosedPeriodicSpectrum hp _ _ a _).mp ha).2
  by_cases hnr : n % 2 = r % 2
  · rw [if_pos hnr, ← (h.distant n hn).rootPolynomial z]
    apply Finset.prod_congr rfl
    intro a ha
    rw [parityAlgebraicMultiplicity_eq_of_root_le hp _ r a
      (by rw [← pairParitySubspace_eq_of_emod_eq n r hnr]; exact hs a ha)]
  · rw [if_neg hnr]
    apply Finset.prod_eq_one
    intro a ha
    rw [parityAlgebraicMultiplicity_eq_zero_of_root_le hp _ r n a (Ne.symm hnr) (hs a ha), pow_zero]

/-- A larger central parity polynomial absorbs precisely the intervening pairs of that parity. -/
theorem CompletePeriodicParityPairs.centralParityPolynomial_eq_mul {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (K : ℕ) (hNK : N ≤ K) (r : ℤ) (z : ℂ) :
    centralParityPolynomial hp (weightedBaseToPair w φ) K r z =
      centralParityPolynomial hp (weightedBaseToPair w φ) N r z *
      ∏ n ∈ centralParityIndices K r \ centralParityIndices N r, (ξ n-z)*(η n-z) := by
  classical
  unfold centralParityPolynomial
  rw [h.counting.centralSpectrum_eq_union K hNK,
    Finset.prod_union (h.counting.central_disjoint_addedDisks K)]
  congr 1
  rw [Finset.prod_biUnion (fun n _ m _ hnm => enclosedPeriodicSpectrum_disjoint hp _ n m hnm),
    centralParityIndices_sdiff, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro n hn
  have hn' : N < n.natAbs := by
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hn
    omega
  exact h.distant_parityPolynomial n hn' r z

/-- Completed central labels give the intrinsic parity polynomial at every larger cutoff. -/
theorem CompletePeriodicParityPairs.central_prod_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (K : ℕ) (hNK : N ≤ K)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∏ n ∈ centralParityIndices K r, (ξ n-z)*(η n-z)) =
      centralParityPolynomial hp (weightedBaseToPair w φ) K r z := by
  rw [← Finset.prod_sdiff (centralParityIndices_mono hNK r), h.central.prod_eq r hr z,
    h.centralParityPolynomial_eq_mul K hNK r z, mul_comm]

end NLS.ZakharovShabat
