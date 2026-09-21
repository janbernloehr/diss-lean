import NLS.ZakharovShabat.BoundaryRootLabeling

/-! # Global algebraic multiplicities in complete boundary sequences
Central-box separation and disjoint distant discs show that every distant
root occurs once; the central multiset supplies all remaining multiplicities.
-/

noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤} {φ : PairSpace p}
variable {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- A central slot lies in the actual central spectral box. -/
theorem central_mem (h : BoundaryRootLabeling b hp φ hφ N ξ) (n : ℤ) (hn : n.natAbs ≤ N) :
    ξ n ∈ centralSpectralBox N :=
  ((b.mem_centralSpectrum hp φ hφ N _).mp ((h.central_iff _).mpr ⟨n,hn,rfl⟩)).2

/-- A distant boundary eigenvalue occurs only at its own signed index. -/
theorem eq_index_of_distant (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (n : ℤ) (hn : N < n.natAbs) (m : ℤ) (he : ξ m = ξ n) : m = n := by
  by_cases hm : N < m.natAbs
  · by_contra hmn
    exact (periodicDisks_disjoint m n hmn).le_bot ⟨(h.distant_spec m hm).1,by rw [he]; exact (h.distant_spec n hn).1⟩
  · have hc := h.central_mem m (by omega)
    rw [he] at hc
    exact False.elim ((centralBox_disjoint_periodicDisk N h.counting.periodic.cutoff_pos n hn).le_bot
      ⟨hc,(h.distant_spec n hn).1⟩)

/-- Every value has a finite set of occurrences in a complete boundary sequence. -/
theorem finite_fiber (h : BoundaryRootLabeling b hp φ hφ N ξ) (z : ℂ) : {n | ξ n = z}.Finite := by
  by_cases hf : ∃ n, N < n.natAbs ∧ ξ n = z
  · obtain ⟨n,hn,hz⟩ := hf
    exact (Set.finite_singleton n).subset (fun m hm => h.eq_index_of_distant n hn m (hm.trans hz.symm))
  · apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
    intro n hn
    have hi : n.natAbs ≤ N := by
      by_contra hlarge
      exact hf ⟨n,by omega,hn⟩
    simp only [Finset.mem_coe,Finset.mem_Icc]
    omega

/-- Each actual eigenvalue occurs with exactly its original boundary algebraic multiplicity. -/
theorem multiplicity (h : BoundaryRootLabeling b hp φ hφ N ξ) (z : ℂ) :
    (∑ᶠ n : ℤ, if ξ n = z then (1 : ℕ) else 0) = b.algebraicMultiplicity hp φ hφ z := by
  by_cases hz : z ∈ b.centralSpectrum hp φ hφ N
  · rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(N : ℤ)) N) (by
      intro n hn
      have he : ξ n = z := by simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hn
      have hi : n.natAbs ≤ N := by
        by_contra hlarge
        have hd := (h.distant_spec n (by omega)).1
        rw [he] at hd
        exact (centralBox_disjoint_periodicDisk N h.counting.periodic.cutoff_pos n (by omega)).le_bot
          ⟨((b.mem_centralSpectrum hp φ hφ N z).mp hz).2,hd⟩
      simp only [Finset.mem_coe,Finset.mem_Icc]
      omega)]
    have hc := congrArg (Multiset.count z) h.central
    rw [b.count_centralRoots,if_pos hz] at hc
    simpa only [Multiset.count_sum',Multiset.count_singleton,eq_comm] using hc
  · by_cases hspec : z ∈ b.spectrum hp φ hφ
    · obtain ⟨n,hn⟩ := (h.exhaustive z).mp hspec
      have hfar : N < n.natAbs := by
        by_contra hlow
        exact hz ((h.central_iff z).mpr ⟨n,by omega,hn⟩)
      rw [finsum_eq_single _ n (by
        intro m hmn
        have hne : ξ m ≠ z := fun hm => hmn (h.eq_index_of_distant n hfar m (hm.trans hn.symm))
        simp only [if_neg hne]),if_pos hn]
      simpa only [hn] using (h.distant_spec n hfar).2.symm
    · have he (n : ℤ) : ξ n ≠ z := fun hn => hspec ((h.exhaustive z).mpr ⟨n,hn⟩)
      simp only [if_neg (he _),finsum_zero]
      symm
      exact (b.algebraicMultiplicity_eq_zero_iff hp φ hφ z).mpr (by simpa [BoundaryCondition.spectrum] using hspec)

end NLS.ZakharovShabat.BoundaryRootLabeling
