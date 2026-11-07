import NLS.Articles.KdVPseudomeasures.SpectralGlobalLabels

/-! Actual global multiplicities and uniqueness of the singular spectral enumeration. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV
namespace SourceHillRealLabeling
variable {r : ℝ} {hr : AdmissiblePredualOrder r} {q : Potential r} {N : ℕ} {ell : ℕ → ℝ}

theorem spectral (h : SourceHillRealLabeling r hr q N ell) (j : ℕ) :
    (ell j:ℂ) ∈ sourceHillSpectrum r hr q.val := (h.spectrum _).mpr ⟨j,rfl⟩

theorem high_slot (h : SourceHillRealLabeling r hr q N ell) (j : ℕ) (hj : 2*N-1 ≤ j) :
    N ≤ (j+1)/2 ∧ (j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2)) := by
  have hN := h.cutoff_ge_two
  omega

theorem tail_above_separator (h : SourceHillRealLabeling r hr q N ell) (j : ℕ) (hj : 2*N-1 ≤ j) :
    freeHillValue N-12*(N:ℝ) < ell j := by
  obtain ⟨p,hl,_⟩ := h.high_pair N le_rfl
  have hp := SourceHillRealPair.above_own_separator r hr q N (by have := h.cutoff_ge_two; omega) p
  have hm := h.monotone hj
  rw [hl] at hm
  exact hp.trans_le hm

/-- An occurrence of a high physical value lies in its own actual pair slots. -/
theorem occurrence_mem_pair (h : SourceHillRealLabeling r hr q N ell)
    (x : ℝ) (hx : freeHillValue N-12*(N:ℝ) ≤ x)
    (n : ℕ) (hn : N ≤ n) (p : SourceHillRealPair r hr q n)
    (hxp : x = p.left ∨ x = p.right) (j : ℕ) (hj : ell j = x) :
    j = 2*n-1 ∨ j = 2*n := by
  have hN := h.cutoff_ge_two
  have hjhigh : 2*N-1 ≤ j := by
    by_contra hjlow
    have hb := h.central_below j (by omega)
    rw [hj] at hb
    linarith
  obtain ⟨hm,hslot⟩ := h.high_slot j hjhigh
  obtain ⟨s,hl,hrr⟩ := h.high_pair ((j+1)/2) hm
  have hxs : x = s.left ∨ x = s.right := by
    rcases hslot with hs | hs
    · exact Or.inl (hj.symm.trans ((congrArg ell hs).trans hl))
    · exact Or.inr (hj.symm.trans ((congrArg ell hs).trans hrr))
  have hmn : (j+1)/2 = n := by
    rcases lt_trichotomy ((j+1)/2) n with hlt | heq | hgt
    · have hsep := SourceHillRealPair.right_lt_left r hr q ((j+1)/2) (by omega) n hlt s p
      rcases hxp with hp | hp <;> rcases hxs with hs | hs <;> linarith [p.ordered,s.ordered]
    · exact heq
    · have hsep := SourceHillRealPair.right_lt_left r hr q n (by omega) ((j+1)/2) hgt p s
      rcases hxp with hp | hp <;> rcases hxs with hs | hs <;> linarith [p.ordered,s.ordered]
  simpa only [hmn] using hslot

/-- Every occurrence set is finite, with its cardinality equal to the ACTUAL physical algebraic multiplicity. -/
theorem finite_support_and_multiplicity (h : SourceHillRealLabeling r hr q N ell) (x : ℝ) :
    (fun j : ℕ => if ell j = x then (1:ℕ) else 0).HasFiniteSupport ∧
      (∑ᶠ j : ℕ, if ell j = x then (1:ℕ) else 0) = sourceHillAlgebraicMultiplicity r hr q.val x := by
  have hN := h.cutoff_ge_two
  by_cases hspec : (x:ℂ) ∈ sourceHillSpectrum r hr q.val
  · by_cases hx : x < freeHillValue N-12*(N:ℝ)
    · have hs : Function.support (fun j : ℕ => if ell j = x then (1:ℕ) else 0) ⊆
          (Finset.range (2*N-1) : Set ℕ) := by
        intro j hj
        have he : ell j = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
          one_ne_zero,imp_false,not_not] using hj
        by_contra hj'
        have hh := h.tail_above_separator j (by simpa only [Finset.mem_coe,Finset.mem_range,not_lt] using hj')
        rw [he] at hh
        linarith
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,h.central_counts x]
      rw [if_pos ((mem_sourceCentralSpectrum r hr q.val N x).mpr ⟨hspec,hx⟩)]
    · obtain ⟨j,hj⟩ := (h.spectrum x).mp hspec
      have hjx : ell j = x := (Complex.ofReal_injective hj).symm
      have hjhigh : 2*N-1 ≤ j := by
        by_contra hjlow
        have hb := h.central_below j (by omega)
        rw [hjx] at hb
        exact hx hb
      obtain ⟨hn,hslot⟩ := h.high_slot j hjhigh
      let n := (j+1)/2
      obtain ⟨p,hl,hrr⟩ := h.high_pair n hn
      have hxp : x = p.left ∨ x = p.right := by
        rcases hslot with hs | hs
        · exact Or.inl (hjx.symm.trans ((congrArg ell hs).trans hl))
        · exact Or.inr (hjx.symm.trans ((congrArg ell hs).trans hrr))
      have hstrip : (x:ℂ) ∈ reducedHillStrip n := by
        rcases hxp with rfl | rfl
        · exact p.left_mem
        · exact p.right_mem
      have hs : Function.support (fun i : ℕ => if ell i = x then (1:ℕ) else 0) ⊆
          ({2*n-1,2*n} : Finset ℕ) := by
        intro i hi
        have he : ell i = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
          one_ne_zero,imp_false,not_not] using hi
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
          h.occurrence_mem_pair x (le_of_not_gt hx) n hn p hxp i he
      refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
      rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair (show 2*n-1 ≠ 2*n by omega),hl,hrr]
      have hc := SourceHillRealPair.multiplicities r hr q n p x hstrip
      simpa only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,
        Complex.ofReal_inj,eq_comm,Nat.add_comm] using hc.symm
  · have hs : Function.support (fun j : ℕ => if ell j = x then (1:ℕ) else 0) ⊆ (∅ : Finset ℕ) := by
      intro j hj
      have he : ell j = x := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,
        one_ne_zero,imp_false,not_not] using hj
      exact (hspec (he ▸ h.spectral j)).elim
    refine ⟨(Finset.finite_toSet _).subset hs,?_⟩
    rw [finsum_eq_sum_of_support_subset _ hs,Finset.sum_empty]
    have hp : ¬0 < sourceHillAlgebraicMultiplicity r hr q.val x := by
      rwa [sourceHillAlgebraicMultiplicity_pos_iff]
    omega

theorem finite_fiber (h : SourceHillRealLabeling r hr q N ell) (x : ℝ) :
    {j : ℕ | ell j = x}.Finite := by
  apply (h.finite_support_and_multiplicity x).1.subset
  intro j hj
  change (if ell j = x then (1:ℕ) else 0) ≠ 0
  have he : ell j = x := hj
  rw [if_pos he]
  exact Nat.one_ne_zero

theorem tail_agrees {M : ℕ} {eta : ℕ → ℝ}
    (h : SourceHillRealLabeling r hr q N ell) (g : SourceHillRealLabeling r hr q M eta)
    (j : ℕ) (hj : 2*(max N M)-1 ≤ j) : ell j = eta j := by
  have hN := h.cutoff_ge_two
  have hM := g.cutoff_ge_two
  have hn : N ≤ (j+1)/2 := by omega
  have hm : M ≤ (j+1)/2 := by omega
  obtain ⟨p,hpl,hpr⟩ := h.high_pair ((j+1)/2) hn
  obtain ⟨s,hsl,hsr⟩ := g.high_pair ((j+1)/2) hm
  have he := SourceHillRealPair.unique r hr q ((j+1)/2) p s
  have hslot : j = 2*((j+1)/2)-1 ∨ j = 2*((j+1)/2) := by omega
  rcases hslot with hs | hs
  · rw [hs,hpl,hsl,he]
  · rw [hs,hpr,hsr,he]

/-- The complete ordered enumeration is independent of the cutoff and every finite/high choice. -/
theorem unique {M : ℕ} {eta : ℕ → ℝ}
    (h : SourceHillRealLabeling r hr q N ell) (g : SourceHillRealLabeling r hr q M eta) : ell = eta := by
  apply NLS.ordered_enumeration_eq_of_finite_exception (· ≤ ·) ell eta (Finset.range (2*(max N M)-1))
  · intro j hj
    exact h.tail_agrees g j (by simpa only [Finset.mem_range,not_lt] using hj)
  · exact g.finite_fiber
  · intro x
    exact (h.finite_support_and_multiplicity x).2.trans (g.finite_support_and_multiplicity x).2.symm
  · exact h.monotone
  · exact g.monotone

end SourceHillRealLabeling
end NLS.Articles.KdVPseudomeasures
