import NLS.KdV.HillHminusOneCanonicalRealLabels

/-! # Intrinsic H^-1 labels depend only on the actual discriminant

Equal entire traces have equal characteristic multiplicities. Transporting
the local high pairs fixes the tails in their exact index slots; global
ordered multiplicity uniqueness then fixes all central labels too.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem hillHminusRadicand_eq_of_discriminant_eq (q p : PeriodOneHminusOne)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    hillHminusRadicand q = hillHminusRadicand p := by
  funext z
  simp only [hillHminusRadicand,congrFun hD z]

theorem HillHminusHighGapPair.of_discriminant_eq
    {q p : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    HillHminusHighGapPair p n r l u := by
  have hR := hillHminusRadicand_eq_of_discriminant_eq q p hD
  refine ⟨h.left_mem,h.right_mem,?_,?_,?_,?_,?_,?_⟩
  · rw [← congrFun hR l]
    exact h.left_zero
  · rw [← congrFun hR u]
    exact h.right_zero
  · intro z hz
    rw [← congrFun hR z]
    exact h.zeros_iff z hz
  · intro z hz
    rw [← hR]
    exact h.multiplicity z hz
  · rw [← congrFun hD l]
    exact h.trace_left
  · rw [← congrFun hD u]
    exact h.trace_right

theorem hillHminusRealLabels_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    hillHminusRealLabels q hq = hillHminusRealLabels p hp := by
  classical
  obtain ⟨N,r,h⟩ := hillHminusRealLabels_spec q hq
  obtain ⟨M,s,g⟩ := hillHminusRealLabels_spec p hp
  apply NLS.ordered_enumeration_eq_of_finite_exception (· ≤ ·)
    (hillHminusRealLabels q hq) (hillHminusRealLabels p hp) (Finset.range (2*(max N M)-1))
  · intro j hj
    have hj' : 2*(max N M)-1 ≤ j := by simpa only [Finset.mem_range,not_lt] using hj
    have hN := h.cutoff_ge_two
    have hM := g.cutoff_ge_two
    have hn : N ≤ (j+1)/2 := by omega
    have hm : M ≤ (j+1)/2 := by omega
    let n : ℕ+ := ⟨(j+1)/2,by omega⟩
    obtain ⟨a,hal,har⟩ := h.high_pair n hn
    obtain ⟨b,hbl,hbr⟩ := g.high_pair n hm
    let t : HillHminusRealHighPair p n r := ⟨a.left,a.right,a.ordered,a.pair.of_discriminant_eq hD⟩
    have he := t.endpoints_unique b
    have hs : j = 2*(n : ℕ)-1 ∨ j = 2*(n : ℕ) := by
      change j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)
      omega
    rcases hs with hs | hs
    · rw [hs,hal,hbl]
      exact he.1
    · rw [hs,har,hbr]
      exact he.2
  · exact finite_fiber_hillHminusRealLabels p hp
  · intro x
    rw [multiplicity_hillHminusRealLabels,multiplicity_hillHminusRealLabels,
      hillHminusRadicand_eq_of_discriminant_eq q p hD]
  · exact monotone_hillHminusRealLabels q hq
  · exact monotone_hillHminusRealLabels p hp

theorem hillHminusLowestRealRoot_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    hillHminusLowestRealRoot q hq = hillHminusLowestRealRoot p hp := by
  rw [← hillHminusRealLabels_zero_eq_lowest q hq,← hillHminusRealLabels_zero_eq_lowest p hp]
  exact congrFun (hillHminusRealLabels_eq_of_discriminant_eq q p hq hp hD) 0

end NLS.KdV
