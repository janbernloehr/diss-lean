import NLS.KdV.HminusOneDirichletComplexControl

/-! Complete ordered COMPLEX native Dirichlet sequences. Internal index j
denotes the original positive index j+1. The actual central multiplicity N
fixes this offset before the high tail is joined. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

/-- A full actual native complex Dirichlet labeling, in original order. -/
structure HillHminusDirichletComplexLabeling (q : PeriodOneHminusOne)
    (u : Coeff 2) (c : ℂ) (N : ℕ) (mu : ℕ → ℂ) : Prop where
  control : HillHminusDirichletComplexControl q u c N
  central : (∑ j ∈ Finset.range N, ({mu j} : Multiset ℂ)) =
    hillHminusDirichletCentralRoots q u c N
  distant : ∀ j : ℕ, N ≤ j → mu j = hillMiuraDirichletEnergy u c (j+1:ℕ)
  ordered : Monotone (fun j => complexLexKey (mu j))

/-- Join the EXACT actual central multiset to the fixed positive high tail.
The whole sequence is lexicographically ordered, including complex central
values and every repeated central eigenvalue. -/
theorem exists_hillHminusDirichletComplexLabeling_of_control
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ) (N : ℕ)
    (h : HillHminusDirichletComplexControl q u c N) :
    ∃ mu : ℕ → ℂ, HillHminusDirichletComplexLabeling q u c N mu := by
  obtain ⟨xi,hxi,horder⟩ := NLS.exists_ordered_finset_multiset_enumeration complexLexLE
    (Finset.range N) (hillHminusDirichletCentralRoots q u c N)
      (by rw [card_hillHminusDirichletCentralRoots q u c h.image N h.counting,Finset.card_range])
  let mu : ℕ → ℂ := fun j => if j < N then xi j else hillMiuraDirichletEnergy u c (j+1:ℕ)
  have hcentral (j : ℕ) (hj : j < N) :
      xi j ∈ hillHminusDirichletCentralSpectrum q u c N := by
    rw [← mem_hillHminusDirichletCentralRoots,← hxi]
    exact Multiset.mem_sum.mpr ⟨j,Finset.mem_range.mpr hj,by simp⟩
  refine ⟨mu,h,?_,fun j hj => by simp only [mu,if_neg (by omega : ¬ j < N)],?_⟩
  · rw [← hxi]
    exact Finset.sum_congr rfl fun j hj => by
      rw [show mu j = xi j by simp only [mu,if_pos (Finset.mem_range.mp hj)]]
  · intro i j hij
    by_cases hi : i < N
    · by_cases hj : j < N
      · change complexLexLE (mu i) (mu j)
        simp only [mu,if_pos hi,if_pos hj]
        exact horder i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij
      · change complexLexLE (mu i) (mu j)
        simp only [mu,if_pos hi,if_neg hj]
        exact complexLexLE_of_re_lt (h.central_re_lt_tail (xi i) (hcentral i hi) (j+1) (by omega))
    · have hj : ¬ j < N := by omega
      change complexLexLE (mu i) (mu j)
      simp only [mu,if_neg hi,if_neg hj]
      rcases lt_or_eq_of_le hij with hij | rfl
      · exact complexLexLE_of_re_lt (h.tail_re_lt (i+1) (j+1) (by omega) (by omega))
      · exact le_rfl

/-- Every complex original unit-period H^-1 source has a complete ordered
native Dirichlet sequence. Neither its labels nor its count are supplied. -/
theorem exists_hillHminusDirichletComplexLabeling (q : PeriodOneHminusOne) :
    ∃ u : Coeff 2, ∃ c : ℂ, ∃ N : ℕ, ∃ mu : ℕ → ℂ,
      HillHminusDirichletComplexLabeling q u c N mu := by
  let C := hillHminusMiuraChartAt q
  have hi := C.image q (mem_hillHminusMiuraChartAt q)
  obtain ⟨N,hN⟩ := exists_hillHminusDirichletComplexControl q (C.lift q) C.energyShift hi
  obtain ⟨mu,hmu⟩ := exists_hillHminusDirichletComplexLabeling_of_control q _ _ N hN
  exact ⟨C.lift q,C.energyShift,N,mu,hmu⟩

namespace HillHminusDirichletComplexLabeling
variable {q : PeriodOneHminusOne} {u : Coeff 2} {c : ℂ} {N : ℕ} {mu : ℕ → ℂ}
variable (h : HillHminusDirichletComplexLabeling q u c N mu)
include h

/-- The first N slots exhaust precisely the ACTUAL central native spectrum. -/
theorem central_iff (e : ℂ) :
    e ∈ hillHminusDirichletCentralSpectrum q u c N ↔ ∃ j : ℕ, j < N ∧ mu j = e := by
  rw [← mem_hillHminusDirichletCentralRoots,← h.central]
  simp only [Multiset.mem_sum,Multiset.mem_singleton,Finset.mem_range]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,he.symm⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,he.symm⟩

/-- The sequence exhausts the ENTIRE original native complex spectrum. -/
theorem exhaustive (e : ℂ) :
    e ∈ singularDirichletSpectrum (periodOneOriginal q) ↔ ∃ j : ℕ, mu j = e := by
  rw [h.control.spectrum_iff e]
  constructor
  · rintro (he | ⟨n,hn,he⟩)
    · obtain ⟨j,_,hj⟩ := (h.central_iff e).mp he
      exact ⟨j,hj⟩
    · refine ⟨n-1,?_⟩
      rw [h.distant (n-1) (by omega),show n-1+1 = n by omega]
      exact he.symm
  · rintro ⟨j,rfl⟩
    by_cases hj : j < N
    · exact Or.inl ((h.central_iff _).mpr ⟨j,hj,rfl⟩)
    · exact Or.inr ⟨j+1,by omega,(h.distant j (by omega))⟩

/-- Every distant value occurs exactly once, at its original positive index. -/
theorem eq_index_of_distant (n : ℕ) (hn : N ≤ n) (m : ℕ) (he : mu m = mu n) : m = n := by
  by_cases hm : m < N
  · have hc := (h.central_iff (mu m)).mpr ⟨m,hm,rfl⟩
    rw [he,h.distant n hn] at hc
    exact (h.control.tail_not_mem_central (n+1) (by omega) hc).elim
  · have hr := congrArg Complex.re he
    rw [h.distant m (by omega),h.distant n hn] at hr
    rcases lt_trichotomy m n with hmn | hmn | hnm
    · have hl := h.control.tail_re_lt (m+1) (n+1) (by omega) (by omega)
      exact (ne_of_lt hl hr).elim
    · exact hmn
    · have hl := h.control.tail_re_lt (n+1) (m+1) (by omega) (by omega)
      exact (ne_of_lt hl hr.symm).elim

/-- Every value has a finite set of occurrences, including repeated central roots. -/
theorem finite_fiber (e : ℂ) : {j | mu j = e}.Finite := by
  by_cases ht : ∃ n, N ≤ n ∧ mu n = e
  · obtain ⟨n,hn,he⟩ := ht
    exact (Set.finite_singleton n).subset fun m hm =>
      h.eq_index_of_distant n hn m (hm.trans he.symm)
  · apply (Finset.range N).finite_toSet.subset
    intro n hn
    exact Finset.mem_range.mpr (by
      by_contra hh
      exact ht ⟨n,by omega,hn⟩)

/-- The complete complex sequence counts EVERY actual native algebraic
multiplicity exactly, including all central associated vectors. -/
theorem multiplicity (e : ℂ) :
    (∑ᶠ j : ℕ, if mu j = e then (1:ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e := by
  by_cases he : e ∈ hillHminusDirichletCentralSpectrum q u c N
  · rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) (by
      intro j hj
      have heq : mu j = e := by simpa only [Function.mem_support,ne_eq,
        ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hj
      apply Finset.mem_range.mpr
      by_contra hlarge
      have ht := h.control.tail_not_mem_central (j+1) (by omega)
      rw [← h.distant j (by omega),heq] at ht
      exact ht he)]
    have hc := congrArg (Multiset.count e) h.central
    rw [count_hillHminusDirichletCentralRoots,if_pos he] at hc
    simpa only [Multiset.count_sum',Multiset.count_singleton,eq_comm] using hc
  · by_cases hs : e ∈ singularDirichletSpectrum (periodOneOriginal q)
    · obtain ⟨n,hn⟩ := (h.exhaustive e).mp hs
      have hfar : N ≤ n := by
        by_contra hlow
        exact he ((h.central_iff e).mpr ⟨n,by omega,hn⟩)
      rw [finsum_eq_single _ n (by
        intro m hmn
        have hne : mu m ≠ e := fun hm => hmn
          (h.eq_index_of_distant n hfar m (hm.trans hn.symm))
        exact if_neg hne),if_pos hn]
      have hm := h.control.tail_multiplicity (n+1) (by omega)
      rw [← h.distant n hfar,hn] at hm
      exact hm.symm
    · have hne (j : ℕ) : mu j ≠ e := fun hj => hs ((h.exhaustive e).mpr ⟨j,hj⟩)
      simp only [if_neg (hne _),finsum_zero]
      symm
      exact Nat.eq_zero_of_not_pos fun hp =>
        hs ((singularDirichletAlgebraicMultiplicity_pos_iff (periodOneOriginal q) e).mp hp)

end HillHminusDirichletComplexLabeling
end NLS.KdV
