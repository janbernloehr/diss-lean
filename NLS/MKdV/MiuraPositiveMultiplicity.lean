import NLS.MKdV.MiuraNLSPositiveEndpoints

/-! # Multiplicities in the ordered positive NLS half-sequence

Strict band separation isolates each occurrence in one original endpoint
pair. Thus counting the positive half requires no arbitrary large cutoff.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical
namespace NLS.MKdV

def miuraNLSPairCount (a : ScalarDomain 2) (x : ℝ) (n : ℤ) : ℕ :=
  ({(miuraNLSLeft a n).re,(miuraNLSRight a n).re} : Multiset ℝ).count x

theorem miuraNLSPairCount_global (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) :
    (∑ᶠ n : ℤ, miuraNLSPairCount a x n) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) x := by
  have hc (n : ℤ) : miuraNLSPairCount a x n =
      ({miuraNLSLeft a n,miuraNLSRight a n} : Multiset ℂ).count (x : ℂ) := by
    have him := miuraNLSEndpoints_real a ha n
    have hL : ((miuraNLSLeft a n).re : ℂ) = miuraNLSLeft a n := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,him.1]
    have hR : ((miuraNLSRight a n).re : ℂ) = miuraNLSRight a n := by
      apply Complex.ext <;> simp only [ofReal_re,ofReal_im,him.2]
    conv_rhs => rw [← hL,← hR]
    simp only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.count_cons,
      Multiset.count_singleton,ofReal_inj]
  calc
    _ = ∑ᶠ n : ℤ, ({miuraNLSLeft a n,miuraNLSRight a n} : Multiset ℂ).count (x : ℂ) :=
      finsum_congr hc
    _ = _ := (canonicalPeriodicEndpoints_spec (by simp) (by norm_num) _
      (periodOnePotential_mem (sobolevSourceInclusion (a,a)))).1.global_multiplicity x

theorem miuraNLSPairCount_other (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    {n m : ℤ} {x : ℝ}
    (hx : (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x) (hm : m ≠ n) :
    miuraNLSPairCount a x m = 0 := by
  by_contra he
  have hmem := Multiset.count_pos.mp (Nat.pos_of_ne_zero he)
  have hx' : (miuraNLSLeft a m).re = x ∨ (miuraNLSRight a m).re = x := by
    simpa only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.mem_cons,
      Multiset.mem_singleton,eq_comm] using hmem
  exact hm (miuraNLSEndpoint_index_unique a ha hx' hx)

theorem miuraNLSMultiplicity_eq_pair (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (n : ℤ) (x : ℝ) (hx : (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x) :
    periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) x =
      miuraNLSPairCount a x n :=
  (miuraNLSPairCount_global a ha x).symm.trans
    (finsum_eq_single _ n (fun m hm => miuraNLSPairCount_other a ha (m := m) hx hm))

theorem miuraPositiveFrequency_fiber_pair (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (n : ℕ) (x : ℝ) (hx : (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x) :
    {j : ℕ | miuraPositiveFrequency a j = x} ⊆ ({2*n-1,2*n} : Finset ℕ) := by
  intro j hj
  have hroot : (miuraNLSLeft a ((j+1)/2 : ℕ)).re = x ∨
      (miuraNLSRight a ((j+1)/2 : ℕ)).re = x := by
    rcases miuraPositiveFrequency_endpoint a j with h | h
    · exact Or.inl (h.symm.trans hj)
    · exact Or.inr (h.symm.trans hj)
  have hi := miuraNLSEndpoint_index_unique a ha hroot hx
  have hi' : (j+1)/2 = n := by exact_mod_cast hi
  simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem miuraPositiveFrequency_finite_fiber (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) :
    {j : ℕ | miuraPositiveFrequency a j = x}.Finite := by
  by_cases h : ∃ j, miuraPositiveFrequency a j = x
  · obtain ⟨j,hj⟩ := h
    have hx : (miuraNLSLeft a ((j+1)/2 : ℕ)).re = x ∨
        (miuraNLSRight a ((j+1)/2 : ℕ)).re = x := by
      rcases miuraPositiveFrequency_endpoint a j with he | he
      · exact Or.inl (he.symm.trans hj)
      · exact Or.inr (he.symm.trans hj)
    exact (Finset.finite_toSet _).subset (miuraPositiveFrequency_fiber_pair a ha _ x hx)
  · have he : {j : ℕ | miuraPositiveFrequency a j = x} = ∅ := by
      ext j
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hj => h ⟨j,hj⟩
    rw [he]
    exact Set.finite_empty

theorem miuraPositiveFrequency_count_pair (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x) :
    (∑ᶠ j : ℕ, if miuraPositiveFrequency a j = x then (1 : ℕ) else 0) = miuraNLSPairCount a x n := by
  have hs : Function.support (fun j : ℕ => if miuraPositiveFrequency a j = x then (1 : ℕ) else 0) ⊆
      ({2*n-1,2*n} : Finset ℕ) := by
    intro j hj
    apply miuraPositiveFrequency_fiber_pair a ha n x hx
    change miuraPositiveFrequency a j = x
    simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hj
  rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega),
    miuraPositiveFrequency_left a n hn,miuraPositiveFrequency_right a n hn]
  simp only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,eq_comm,Nat.add_comm]

theorem miuraPositiveFrequency_count_ground (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ)
    (hx : (miuraNLSLeft a 0).re = x ∨ (miuraNLSRight a 0).re = x) :
    (∑ᶠ j : ℕ, if miuraPositiveFrequency a j = x then (1 : ℕ) else 0) =
      if (miuraNLSRight a 0).re = x then 1 else 0 := by
  rw [finsum_eq_single _ 0 (fun j hj => ?_),miuraPositiveFrequency_zero]
  apply if_neg
  intro he
  have hm := miuraPositiveFrequency_fiber_pair a ha 0 x hx he
  simp only [mul_zero,zero_tsub,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,or_self] at hm
  exact hj hm

theorem miuraPositiveFrequency_count_pos (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) (hxpos : 0 < x) :
    (∑ᶠ j : ℕ, if miuraPositiveFrequency a j = x then (1 : ℕ) else 0) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) x := by
  by_cases hex : ∃ n : ℤ, (miuraNLSLeft a n).re = x ∨ (miuraNLSRight a n).re = x
  · obtain ⟨n,hx⟩ := hex
    have hn : 0 ≤ n := by
      by_contra he
      have hR := miuraNLSRight_neg a ha (lt_of_not_ge he)
      have hw := miuraNLSEndpoints_within a n
      rcases hx with hx | hx <;> linarith
    lift n to ℕ using hn
    by_cases hn0 : n = 0
    · subst n
      rw [miuraPositiveFrequency_count_ground a ha x hx,miuraNLSMultiplicity_eq_pair a ha 0 x hx]
      have hLne : x ≠ (miuraNLSLeft a 0).re := by
        have h := congrArg Complex.re (miuraNLSEndpoints_reflection a 0).1
        simp only [neg_zero,neg_re] at h
        have hR := miuraNLSRight_zero_nonnegative a
        linarith
      simp only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.count_cons,
        Multiset.count_singleton,if_neg hLne,add_zero,eq_comm]
    · exact (miuraPositiveFrequency_count_pair a ha n (by omega) x hx).trans
        (miuraNLSMultiplicity_eq_pair a ha n x hx).symm
  · have hν (j : ℕ) : (if miuraPositiveFrequency a j = x then (1 : ℕ) else 0) = 0 := by
      apply if_neg
      intro hj
      apply hex
      refine ⟨((j+1)/2 : ℕ),?_⟩
      rcases miuraPositiveFrequency_endpoint a j with h | h
      · exact Or.inl (h.symm.trans hj)
      · exact Or.inr (h.symm.trans hj)
    have hN (n : ℤ) : miuraNLSPairCount a x n = 0 := by
      by_contra he
      have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero he)
      apply hex
      refine ⟨n,?_⟩
      simpa only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.mem_cons,
        Multiset.mem_singleton,eq_comm] using hm
    have hzero := (miuraNLSPairCount_global a ha x).symm.trans
      (finsum_eq_zero_of_forall_eq_zero hN)
    exact (finsum_eq_zero_of_forall_eq_zero hν).trans hzero.symm

theorem miuraPositiveFrequency_count_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (∑ᶠ j : ℕ, if miuraPositiveFrequency a j = 0 then (1 : ℕ) else 0) =
      if (miuraNLSRight a 0).re = 0 then 1 else 0 := by
  rw [finsum_eq_single _ 0 (fun j hj => ?_),miuraPositiveFrequency_zero]
  apply if_neg
  intro he
  have hp := miuraPositiveFrequency_pos a ha (Nat.pos_of_ne_zero hj)
  rw [he] at hp
  exact lt_irrefl _ hp

theorem miuraPositiveFrequency_zero_multiplicity (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 =
      2*(∑ᶠ j : ℕ, if miuraPositiveFrequency a j = 0 then (1 : ℕ) else 0) := by
  have hoff (n : ℤ) (hn : n ≠ 0) : miuraNLSPairCount a 0 n = 0 := by
    by_contra he
    have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero he)
    have hx : (miuraNLSLeft a n).re = 0 ∨ (miuraNLSRight a n).re = 0 := by
      simpa only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.mem_cons,
        Multiset.mem_singleton,eq_comm] using hm
    have hw := miuraNLSEndpoints_within a n
    rcases lt_or_gt_of_ne hn with h | h
    · have hs := miuraNLSRight_neg a ha h
      rcases hx with hx | hx <;> linarith
    · have hs := miuraNLSLeft_pos a ha h
      rcases hx with hx | hx <;> linarith
  have hM := (miuraNLSPairCount_global a ha 0).symm.trans (finsum_eq_single _ 0 hoff)
  have href := congrArg Complex.re (miuraNLSEndpoints_reflection a 0).1
  simp only [neg_zero,neg_re] at href
  simp only [ofReal_zero] at hM
  rw [hM,miuraPositiveFrequency_count_zero a ha]
  have hL : (0 : ℝ) = (miuraNLSLeft a 0).re ↔ (miuraNLSRight a 0).re = 0 := by
    rw [href]
    constructor <;> intro h <;> linarith
  simp only [miuraNLSPairCount,Multiset.insert_eq_cons,Multiset.count_cons,
    Multiset.count_singleton,hL,eq_comm (a := (0 : ℝ)) (b := (miuraNLSRight a 0).re)]
  by_cases hR : (miuraNLSRight a 0).re = 0 <;> simp [hR]

end NLS.MKdV
