import NLS.ZakharovShabat.CentralPeriodicRoots
import NLS.SequenceSpaces.OrderedPairedEnumeration
import NLS.ComplexAnalysis.LexicographicOrder

/-!
# Ordered central periodic endpoints

Forget the arbitrary grouping within the two parity multisets and sort
all central roots together. The resulting paired enumeration retains all
original algebraic multiplicities. Its index parity is not asserted here.
-/

noncomputable section
open Set
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two central slots per index enumerate the full original root multiset. -/
structure CentralPeriodicLabeling (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ) : Prop where
  roots : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ)) = centralPeriodicRoots hp φ N

/-- A parity-respecting central labeling also enumerates the full multiset. -/
theorem CentralParityLabeling.toPeriodic {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralParityLabeling hp φ N ξ η) (hφ : φ ∈ pairParitySubspace 0) :
    CentralPeriodicLabeling hp φ N ξ η := by
  constructor
  rw [centralPeriodicRoots_eq_parity_add hp φ hφ N, ← h.even, ← h.odd,
    sum_centralParityIndices_zero_add_one]

/-- Central endpoints enumerate exactly the original central spectrum. -/
theorem CentralPeriodicLabeling.root_iff {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralPeriodicLabeling hp φ N ξ η) (z : ℂ) :
    (∃ n : ℤ, n.natAbs ≤ N ∧ (ξ n = z ∨ η n = z)) ↔ z ∈ centralPeriodicSpectrum hp φ N := by
  rw [← mem_centralPeriodicRoots, ← h.roots]
  simp only [Multiset.mem_sum, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, Finset.mem_Icc]
  constructor
  · rintro ⟨n,hn,hz⟩
    exact ⟨n,by omega,by simpa only [eq_comm] using hz⟩
  · rintro ⟨n,hn,hz⟩
    exact ⟨n,by omega,by simpa only [eq_comm] using hz⟩

/-- Original analytic multiplicities are retained by the paired central enumeration. -/
theorem CentralPeriodicLabeling.count_eq {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralPeriodicLabeling hp φ N ξ η) (z : ℂ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ).count z) =
      if z ∈ centralPeriodicSpectrum hp φ N then periodicAlgebraicMultiplicity hp φ z else 0 := by
  rw [← Multiset.count_sum', h.roots, count_centralPeriodicRoots]

/-- Actual central roots have an ordered paired enumeration, retaining all repetitions. -/
theorem exists_ordered_centralPeriodicLabeling (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (hc : PeriodicCountingData hp φ N) :
    ∃ ξ η : ℤ → ℂ, CentralPeriodicLabeling hp φ N ξ η ∧
      (∀ n : ℤ, n.natAbs ≤ N → complexLexLE (ξ n) (η n)) ∧
      ∀ i : ℤ, i.natAbs ≤ N → ∀ j : ℤ, j.natAbs ≤ N → i < j → complexLexLE (η i) (ξ j) := by
  obtain ⟨ξ,η,hr,hw,hc⟩ := NLS.exists_ordered_paired_multiset_enumeration complexLexLE
    (Finset.Icc (-(N : ℤ)) N) (centralPeriodicRoots hp φ N) hc.card_centralPeriodicRoots
  refine ⟨ξ,η,⟨hr⟩,fun n hn => hw n ?_,fun i hi j hj hij => hc i ?_ j ?_ hij⟩ <;>
    simp only [Finset.mem_Icc] <;> omega

end NLS.ZakharovShabat
