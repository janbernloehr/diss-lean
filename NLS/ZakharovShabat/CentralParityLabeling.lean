import NLS.ZakharovShabat.CentralParityPolynomials
import NLS.ZakharovShabat.PeriodicCounting
import NLS.SequenceSpaces.FinitePairedEnumeration

/-!
# Complete central pair labels respecting actual parity multiplicities

The central parity counts supply two slots per signed free index. Enumeration
assigns the actual central roots to these slots, retaining repetitions and
allowing a common eigenvalue in both parity sectors. No continuity of these
individual labels is asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two central labels per index, with the actual root multiset in each parity. -/
structure CentralParityLabeling (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ) : Prop where
  even : (∑ n ∈ centralParityIndices N 0, ({ξ n, η n} : Multiset ℂ)) = centralParityRoots hp φ N 0
  odd : (∑ n ∈ centralParityIndices N 1, ({ξ n, η n} : Multiset ℂ)) = centralParityRoots hp φ N 1

/-- Actual central counts provide exactly two slots for every index of a given parity. -/
theorem PeriodicCountingData.card_centralParityRoots {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ}
    (hc : PeriodicCountingData hp φ N) (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) :
    (centralParityRoots hp φ N r).card = 2*(centralParityIndices N r).card := by
  have h := hc.central_parity hφ r
  rw [centralSpectralProjection, range_periodicClusterProjection,
    finrank_periodicClusterSpace_inf_parity hp φ hφ] at h
  rw [NLS.ZakharovShabat.card_centralParityRoots, h, card_centralParityIndices]
  split_ifs <;> omega

/-- Every counted even potential has a central labeling with its exact parity root multisets. -/
theorem exists_centralParityLabeling (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    (N : ℕ) (hc : PeriodicCountingData hp φ N) : ∃ ξ η : ℤ → ℂ, CentralParityLabeling hp φ N ξ η := by
  classical
  obtain ⟨ξ₀, η₀, h₀⟩ := NLS.exists_paired_multiset_enumeration (centralParityIndices N 0)
    (centralParityRoots hp φ N 0) (hc.card_centralParityRoots hφ 0)
  obtain ⟨ξ₁, η₁, h₁⟩ := NLS.exists_paired_multiset_enumeration (centralParityIndices N 1)
    (centralParityRoots hp φ N 1) (hc.card_centralParityRoots hφ 1)
  refine ⟨fun n => if n % 2 = 0 then ξ₀ n else ξ₁ n,
    fun n => if n % 2 = 0 then η₀ n else η₁ n, ?_⟩
  constructor
  · rw [← h₀]
    apply Finset.sum_congr rfl
    intro n hn
    have he : n % 2 = 0 := (Finset.mem_filter.mp hn).2
    simp only [if_pos he]
  · rw [← h₁]
    apply Finset.sum_congr rfl
    intro n hn
    have he : n % 2 = 1 := (Finset.mem_filter.mp hn).2
    simp only [if_neg (by omega : n % 2 ≠ 0)]

/-- The two stored multiset identities can be used with either source parity. -/
theorem CentralParityLabeling.sum_eq {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralParityLabeling hp φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) :
    (∑ n ∈ centralParityIndices N r, ({ξ n, η n} : Multiset ℂ)) = centralParityRoots hp φ N r := by
  rcases hr with rfl | rfl
  · exact h.even
  · exact h.odd

/-- The central pair labels enumerate precisely the roots with positive actual parity multiplicity. -/
theorem CentralParityLabeling.root_iff {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralParityLabeling hp φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∃ n ∈ centralParityIndices N r, ξ n = z ∨ η n = z) ↔
      z ∈ centralPeriodicSpectrum hp φ N ∧ 0 < parityAlgebraicMultiplicity hp φ r z := by
  rw [← mem_centralParityRoots, ← h.sum_eq r hr]
  simp [eq_comm]

/-- Every root product computed from central pair labels equals the intrinsic parity polynomial. -/
theorem CentralParityLabeling.prod_eq {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralParityLabeling hp φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∏ n ∈ centralParityIndices N r, (ξ n-z)*(η n-z)) = centralParityPolynomial hp φ N r z := by
  have hm := prod_centralParityRoots hp φ N r z
  rw [← h.sum_eq r hr] at hm
  have he (s : Finset ℤ) : ((∑ n ∈ s, ({ξ n, η n} : Multiset ℂ)).map (fun ζ => ζ-z)).prod =
      ∏ n ∈ s, (ξ n-z)*(η n-z) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      have hpair : (({ξ n, η n} : Multiset ℂ).map (fun ζ => ζ-z)).prod = (ξ n-z)*(η n-z) := by simp
      rw [Finset.sum_insert hn, Multiset.map_add, Multiset.prod_add, hpair, ih, Finset.prod_insert hn]
  rwa [he] at hm

end NLS.ZakharovShabat
