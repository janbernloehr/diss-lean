import NLS.ZakharovShabat.PeriodicEndpointLabeling
import NLS.ZakharovShabat.CentralSpectrumCutoffs

/-!
# Cutoff growth for full periodic endpoint labels

Each distant pair is the actual two-root multiset of its disc. Enlarging
the center absorbs exactly the intervening pairs, so the same complete
sequence enumerates the full central multiset at every larger cutoff.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The distant endpoint multiset is exactly its original disc spectrum with algebraic multiplicity. -/
theorem PeriodicEndpointPair.multiset_eq_roots {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {x y : ℂ}
    (h : PeriodicEndpointPair hp φ n x y) :
    ({x,y} : Multiset ℂ) = ∑ z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4),
      Multiset.replicate (periodicAlgebraicMultiplicity hp φ z) z := by
  apply Multiset.ext.mpr
  intro z
  simp only [Multiset.count_sum',Multiset.count_replicate]
  simp only [Finset.sum_ite_eq']
  by_cases hz : z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4)
  · rw [if_pos hz]
    exact (h.multiplicity_eq_count z (refinedResonantDisk_subset_strip n
      ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hz).2)).symm
  · rw [if_neg hz]
    apply Multiset.count_eq_zero.mpr
    intro hm
    have hm' : z = x ∨ z = y := by simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] using hm
    apply hz
    rcases hm' with rfl | rfl
    · exact (mem_enclosedPeriodicSpectrum hp φ _ z _).mpr
        ⟨(h.spectrum_iff z (refinedResonantDisk_subset_strip n h.left_mem)).mpr (Or.inl rfl),h.left_mem⟩
    · exact (mem_enclosedPeriodicSpectrum hp φ _ z _).mpr
        ⟨(h.spectrum_iff z (refinedResonantDisk_subset_strip n h.right_mem)).mpr (Or.inr rfl),h.right_mem⟩

/-- Two complete pairs in the same distant disc have the same multiset, including multiplicities. -/
theorem PeriodicEndpointPair.multiset_eq {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {x y a b : ℂ}
    (h : PeriodicEndpointPair hp φ n x y) (h' : PeriodicEndpointPair hp φ n a b) :
    ({x,y} : Multiset ℂ) = {a,b} := h.multiset_eq_roots.trans h'.multiset_eq_roots.symm

/-- A larger central multiset absorbs exactly the intervening distant endpoint pairs. -/
theorem PeriodicEndpointLabeling.centralRoots_eq_add {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η)
    (K : ℕ) (hNK : N ≤ K) :
    centralPeriodicRoots hp φ K = centralPeriodicRoots hp φ N +
      ∑ n ∈ Finset.Icc (-(K : ℤ)) K \ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ) := by
  unfold centralPeriodicRoots
  rw [h.counting.centralSpectrum_eq_union K hNK, Finset.sum_union (h.counting.central_disjoint_addedDisks K)]
  congr 1
  rw [Finset.sum_biUnion (fun n _ m _ hnm => enclosedPeriodicSpectrum_disjoint hp φ n m hnm)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : N < n.natAbs := by simp only [Finset.mem_sdiff,Finset.mem_Icc] at hn; omega
  exact (h.distant n hn').multiset_eq_roots.symm

/-- The same endpoint sequence enumerates the full central multiset at every larger cutoff. -/
theorem PeriodicEndpointLabeling.central_at_larger_cutoff {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η)
    (K : ℕ) (hNK : N ≤ K) : CentralPeriodicLabeling hp φ K ξ η := by
  constructor
  have hs : Finset.Icc (-(N : ℤ)) N ⊆ Finset.Icc (-(K : ℤ)) K := by
    intro n hn
    simp only [Finset.mem_Icc] at *
    omega
  rw [← Finset.sum_sdiff hs, h.central.roots,
    h.centralRoots_eq_add K hNK, add_comm]

/-- With counting data at a larger cutoff, the entire endpoint labeling enlarges unchanged. -/
theorem PeriodicEndpointLabeling.enlarge {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η)
    (K : ℕ) (hNK : N ≤ K) (hc : PeriodicCountingData hp φ K) : PeriodicEndpointLabeling hp φ K ξ η :=
  ⟨hc,h.central_at_larger_cutoff K hNK,fun n hn => h.distant n (by omega),h.left_displacement,h.right_displacement⟩

end NLS.ZakharovShabat
