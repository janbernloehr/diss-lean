import NLS.ZakharovShabat.LinearWeightEndpointCounts

/-! # Recovering an endpoint pair from its strip occurrence count

Once both indexed slots belong to a strip with exactly two occurrences,
they exhaust its spectrum and carry every original algebraic multiplicity.
-/
noncomputable section
open scoped Classical ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two known slots in a two-occurrence strip give the complete original endpoint pair. -/
theorem PeriodicEndpointLabeling.toPair_of_strip_count
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (hl : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p) (n : ℤ) (hn : n.natAbs ≤ N)
    (hcount : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).card = 2)
    (hx : ξ n ∈ refinedResonantDisk n) (hy : η n ∈ refinedResonantDisk n) :
    PeriodicEndpointPair hp φ n (ξ n) (η n) := by
  let s := centralPeriodicSlots N
  let a : ℤ ×ₗ Fin 2 := toLex (n,0)
  let b : ℤ ×ₗ Fin 2 := toLex (n,1)
  have hab : a ≠ b := by
    intro h
    have he := congrArg (fun k : ℤ ×ₗ Fin 2 => (ofLex k).2) h
    norm_num [a,b] at he
  have hsub : ({a,b} : Finset (ℤ ×ₗ Fin 2)) ⊆ s.filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simpa [s,a] using hn,
        by simpa [a] using refinedResonantDisk_subset_strip n hx⟩
    · exact Finset.mem_filter.mpr ⟨by simpa [s,b] using hn,
        by simpa [b] using refinedResonantDisk_subset_strip n hy⟩
  have hpair : ({a,b} : Finset (ℤ ×ₗ Fin 2)) = s.filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n) :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [hab] using hcount.le)
  have hm (z : ℂ) (hz : z ∈ resonantStrip n) : periodicAlgebraicMultiplicity hp φ z = ({ξ n,η n} : Multiset ℂ).count z := by
    have hS : ∀ v ∈ ({z} : Set ℂ), |v.re| ≤ centralCircleRadius N := by
      intro v hv
      have hvz : v = z := Set.mem_singleton_iff.mp hv
      subst v
      exact abs_re_le_centralRadius_of_mem_resonantStrip N n hn z hz
    have h := hl.analyticZeroCount_eq_card_filter_slots hp1 ({z} : Set ℂ) hS
    have hsingle : analyticZeroCount (canonicalPeriodicProduct hp φ) ({z} : Set ℂ) =
        analyticOrderNatAt (canonicalPeriodicProduct hp φ) z := by
      rw [analyticZeroCount_eq_sum {z} (by simp) (by intro v hv; simpa using hv.1)]
      simp
    rw [hsingle,analyticOrderNatAt_canonicalPeriodicProduct hp hp1 φ z] at h
    simp only [Set.mem_singleton_iff] at h
    have he : s.filter (fun k => periodicEndpointSlot ξ η k = z) =
        (s.filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).filter (fun k => periodicEndpointSlot ξ η k = z) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk,hkz⟩
        exact ⟨⟨hk,hkz ▸ hz⟩,hkz⟩
      · rintro ⟨⟨hk,_⟩,hkz⟩
        exact ⟨hk,hkz⟩
    change periodicAlgebraicMultiplicity hp φ z = (s.filter (fun k => periodicEndpointSlot ξ η k = z)).card at h
    rw [he,← hpair] at h
    rw [h]
    simp [Finset.card_filter, Finset.sum_pair hab, a, b,
      Multiset.count_cons, Multiset.count_singleton, eq_comm, add_comm]
  refine ⟨hx,hy,?_,hm⟩
  intro z hz
  rw [← periodicAlgebraicMultiplicity_pos_iff hp φ z,hm z hz,Multiset.count_pos]
  simp

end NLS.ZakharovShabat
