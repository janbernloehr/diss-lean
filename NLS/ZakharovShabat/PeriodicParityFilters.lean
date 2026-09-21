import NLS.ZakharovShabat.FiniteDiscriminant
import NLS.ZakharovShabat.CentralPeriodicRoots

/-!
# Recovering parity multisets by discriminant levels

The two discriminant levels are disjoint. Each level therefore carries
all of its root's original algebraic multiplicity, while the opposite
sector contributes zero. Filtering the full central multiset recovers
the exact original parity multiset.
-/

noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A parity sector carries the full algebraic multiplicity exactly at its discriminant level. -/
theorem parityAlgebraicMultiplicity_eq_ite_discriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    parityAlgebraicMultiplicity hp φ r z =
      if canonicalDiscriminant hp φ z = (if r % 2 = 0 then 2 else -2)
      then periodicAlgebraicMultiplicity hp φ z else 0 := by
  have hlevels := canonicalDiscriminant_parity_levels_finite hp hp1 φ heven z
  rcases hr with rfl | rfl
  · simp only [Int.zero_emod, if_true]
    by_cases hz : canonicalDiscriminant hp φ z = 2
    · have ho : parityAlgebraicMultiplicity hp φ 1 z = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpz
        have he := hlevels.2.mpr hpz
        rw [hz] at he
        norm_num at he
      rw [if_pos hz, periodicAlgebraicMultiplicity_eq_parity_sum hp φ heven z, ho, add_zero]
    · rw [if_neg hz]
      exact Nat.eq_zero_of_not_pos (fun hm => hz (hlevels.1.mpr hm))
  · simp only [Int.one_emod_two, one_ne_zero, if_false]
    by_cases hz : canonicalDiscriminant hp φ z = -2
    · have he : parityAlgebraicMultiplicity hp φ 0 z = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpz
        have ho := hlevels.1.mpr hpz
        rw [hz] at ho
        norm_num at ho
      rw [if_pos hz, periodicAlgebraicMultiplicity_eq_parity_sum hp φ heven z, he, zero_add]
    · rw [if_neg hz]
      exact Nat.eq_zero_of_not_pos (fun hm => hz (hlevels.2.mpr hm))

/-- Filtering the full central root multiset by a discriminant level recovers exact parity multiplicities. -/
theorem centralParityRoots_eq_filter_discriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (N : ℕ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    centralParityRoots hp φ N r = (centralPeriodicRoots hp φ N).filter
      (fun z => canonicalDiscriminant hp φ z = (if r % 2 = 0 then 2 else -2)) := by
  apply Multiset.ext.mpr
  intro z
  rw [count_centralParityRoots,Multiset.count_filter,count_centralPeriodicRoots,
    parityAlgebraicMultiplicity_eq_ite_discriminant hp hp1 φ heven r hr z]
  by_cases hc : z ∈ centralPeriodicSpectrum hp φ N <;>
    by_cases hl : canonicalDiscriminant hp φ z = (if r % 2 = 0 then 2 else -2) <;> simp [hc,hl]

end NLS.ZakharovShabat
