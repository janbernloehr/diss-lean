import NLS.ZakharovShabat.CentralParityLabeling

/-!
# Full central periodic root multisets

The full multiset records the original algebraic multiplicity of each
central periodic eigenvalue. It is the sum of the parity multisets and
has two slots per signed central index under the actual counting theorem.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All central periodic roots, repeated with their original algebraic multiplicities. -/
def centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) : Multiset ℂ :=
  ∑ z ∈ centralPeriodicSpectrum hp φ N, Multiset.replicate (periodicAlgebraicMultiplicity hp φ z) z

/-- The count of a value is precisely its original central algebraic multiplicity. -/
theorem count_centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    (centralPeriodicRoots hp φ N).count z =
      if z ∈ centralPeriodicSpectrum hp φ N then periodicAlgebraicMultiplicity hp φ z else 0 := by
  simp [centralPeriodicRoots, Multiset.count_sum', Multiset.count_replicate]

/-- The full central multiset has the total algebraic multiplicity of the central cluster. -/
theorem card_centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    (centralPeriodicRoots hp φ N).card =
      ∑ z ∈ centralPeriodicSpectrum hp φ N, periodicAlgebraicMultiplicity hp φ z := by
  simp [centralPeriodicRoots]

/-- Every central spectral value occurs, and no other value occurs. -/
theorem mem_centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    z ∈ centralPeriodicRoots hp φ N ↔ z ∈ centralPeriodicSpectrum hp φ N := by
  rw [← Multiset.count_pos, count_centralPeriodicRoots]
  by_cases hz : z ∈ centralPeriodicSpectrum hp φ N
  · simp only [hz, iff_true]
    exact (periodicAlgebraicMultiplicity_pos_iff hp φ z).mpr
      ((mem_centralPeriodicSpectrum hp φ N z).mp hz).1
  · simp [hz]

/-- Even and odd multiplicities add to the full central root multiset. -/
theorem centralPeriodicRoots_eq_parity_add (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) :
    centralPeriodicRoots hp φ N = centralParityRoots hp φ N 0 + centralParityRoots hp φ N 1 := by
  apply Multiset.ext.mpr
  intro z
  simp only [count_centralPeriodicRoots, Multiset.count_add, count_centralParityRoots]
  split_ifs
  · exact periodicAlgebraicMultiplicity_eq_parity_sum hp φ hφ z
  · rfl

/-- The actual counting theorem gives exactly two slots at every central index. -/
theorem PeriodicCountingData.card_centralPeriodicRoots {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ}
    (h : PeriodicCountingData hp φ N) :
    (centralPeriodicRoots hp φ N).card = 2*(Finset.Icc (-(N : ℤ)) N).card := by
  rw [NLS.ZakharovShabat.card_centralPeriodicRoots, h.central_multiplicity, Int.card_Icc]
  omega

/-- Summing both parity parts recovers the complete central sum. -/
theorem sum_centralParityIndices_zero_add_one (N : ℕ) (f : ℤ → Multiset ℂ) :
    (∑ n ∈ centralParityIndices N 0, f n) + (∑ n ∈ centralParityIndices N 1, f n) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f n := by
  simp only [centralParityIndices, Finset.sum_filter, Int.zero_emod, Int.one_emod_two]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n % 2 = 0
  · simp [hn]
  · have hn1 : n % 2 = 1 := by omega
    simp [hn1]

end NLS.ZakharovShabat
