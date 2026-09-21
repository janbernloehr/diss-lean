import NLS.ZakharovShabat.BoundaryRootMultiplicity
import NLS.ZakharovShabat.CentralSpectrumCutoffs

/-!
# Enlarging the central block of a complete boundary sequence
The same sequence gives the exact central multiset at every larger cutoff.
Its global multiplicities count the newly absorbed distant simple roots.
-/

noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤} {φ : PairSpace p}
variable {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- Membership in a larger central box is exactly membership of the signed index in its block. -/
theorem mem_larger_central_iff (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (K : ℕ) (hK : N ≤ K) (n : ℤ) : ξ n ∈ centralSpectralBox K ↔ n.natAbs ≤ K := by
  have hKpos : 0 < K := h.counting.periodic.cutoff_pos.trans_le hK
  constructor
  · intro hz
    by_contra hn
    exact (centralBox_disjoint_periodicDisk K hKpos n (by omega)).le_bot
      ⟨hz,(h.distant_spec n (by omega)).1⟩
  · intro hn
    by_cases hnN : n.natAbs ≤ N
    · exact centralSpectralBox_mono hK (h.central_mem n hnN)
    · have hrK : Real.pi/4 ≤ (K : ℝ) := by
        have h1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
        linarith [Real.pi_le_four]
      exact (smallDisk_central_selection K n le_rfl hrK (h.distant_spec n (by omega)).1).2.mpr hn

/-- At each larger cutoff the same labels recover the actual central multiset with multiplicities. -/
theorem central_at_larger_cutoff (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (K : ℕ) (hK : N ≤ K) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) K, ({ξ n} : Multiset ℂ)) = b.centralRoots hp φ hφ K := by
  apply Multiset.ext.mpr
  intro z
  rw [Multiset.count_sum',b.count_centralRoots]
  by_cases hz : z ∈ b.centralSpectrum hp φ hφ K
  · rw [if_pos hz,← h.multiplicity z]
    have hs : Function.support (fun n : ℤ => if ξ n = z then (1 : ℕ) else 0) ⊆
        (Finset.Icc (-(K : ℤ)) K : Set ℤ) := by
      intro n hn
      have he : ξ n = z := by
        simpa only [Function.mem_support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hn
      have hnK := (h.mem_larger_central_iff K hK n).mp (by
        rw [he]
        exact ((b.mem_centralSpectrum hp φ hφ K z).mp hz).2)
      simp only [Finset.mem_coe,Finset.mem_Icc]
      omega
    rw [finsum_eq_sum_of_support_subset _ hs]
    simp only [Multiset.count_singleton,eq_comm]
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro n hn
    have hnK : n.natAbs ≤ K := by simp only [Finset.mem_Icc] at hn; omega
    have he : ξ n ≠ z := by
      intro he
      apply hz
      rw [← he]
      exact (b.mem_centralSpectrum hp φ hφ K (ξ n)).mpr
        ⟨(h.exhaustive _).mpr ⟨n,rfl⟩,(h.mem_larger_central_iff K hK n).mpr hnK⟩
    simp only [Multiset.count_singleton,if_neg (Ne.symm he)]

/-- At any larger admissible cutoff, the complete labeling remains unchanged. -/
theorem enlarge (h : BoundaryRootLabeling b hp φ hφ N ξ) (K : ℕ) (hK : N ≤ K)
    (hc : BoundaryCountingData hp φ hφ K) : BoundaryRootLabeling b hp φ hφ K ξ :=
  ⟨hc,h.central_at_larger_cutoff K hK,fun n hn => h.distant n (by omega),h.displacement⟩

end NLS.ZakharovShabat.BoundaryRootLabeling
