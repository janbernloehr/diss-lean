import NLS.ZakharovShabat.CentralBoundaryRoots
import NLS.SequenceSpaces.FiniteModification
import NLS.ZakharovShabat.BoundarySpectrum

/-!
# Complete actual boundary root labelings
Finite central roots replace the central trace values. The distant labels
are the unique simple boundary eigenvalues, and the full sequence retains
an lp displacement from the signed free lattice.
-/

noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complete boundary labeling with actual central multiplicities and fixed distant branches. -/
structure BoundaryRootLabeling (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) (ξ : ℤ → ℂ) : Prop where
  counting : BoundaryCountingData hp φ hφ N
  central : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = b.centralRoots hp φ hφ N
  distant : ∀ n : ℤ, N < n.natAbs → ξ n = b.eigenvalue hp φ n
  displacement : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p

/-- Counted central roots and an lp high branch give a complete actual boundary labeling. -/
theorem exists_boundaryRootLabeling (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) (hc : BoundaryCountingData hp φ hφ N)
    (hd : Memℓp (fun n => b.eigenvalue hp φ n-(Real.pi : ℂ)*n) p) :
    ∃ ξ : ℤ → ℂ, BoundaryRootLabeling b hp φ hφ N ξ := by
  obtain ⟨α,hα⟩ := b.exists_centralRootLabeling hp φ hφ N hc
  let ξ : ℤ → ℂ := fun n => if N < n.natAbs then b.eigenvalue hp φ n else α n
  refine ⟨ξ,hc,?_,fun n hn => by simp only [ξ,if_pos hn],?_⟩
  · rw [← hα]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ¬ N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [ξ,if_neg hn']
  · apply NLS.memℓp_of_eq_outside_finset hd (Finset.Icc (-(N : ℤ)) N)
    intro n hn
    have hn' : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [ξ,if_pos hn']

namespace BoundaryRootLabeling
variable {b : BoundaryCondition} {hp : p ≠ ⊤} {φ : PairSpace p}
variable {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- The central slots are precisely the actual boundary eigenvalues in the central box. -/
theorem central_iff (h : BoundaryRootLabeling b hp φ hφ N ξ) (z : ℂ) :
    z ∈ b.centralSpectrum hp φ hφ N ↔ ∃ n : ℤ, n.natAbs ≤ N ∧ ξ n = z := by
  rw [← b.mem_centralRoots hp φ hφ N z,← h.central]
  simp only [Multiset.mem_sum,Multiset.mem_singleton,Finset.mem_Icc]
  constructor
  · rintro ⟨n,hn,he⟩; exact ⟨n,by omega,he.symm⟩
  · rintro ⟨n,hn,he⟩; exact ⟨n,by omega,he.symm⟩

/-- The complete sequence exhausts the actual boundary spectrum, including all central values. -/
theorem exhaustive (h : BoundaryRootLabeling b hp φ hφ N ξ) (z : ℂ) :
    z ∈ b.spectrum hp φ hφ ↔ ∃ n : ℤ, ξ n = z := by
  constructor
  · intro hz
    rcases h.counting.spectrum_subset b hz with hcentral | hdistant
    · obtain ⟨n,_,hn⟩ := (h.central_iff z).mp ((b.mem_centralSpectrum hp φ hφ N z).mpr ⟨hz,hcentral⟩)
      exact ⟨n,hn⟩
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hdistant
      obtain ⟨hn,hzdisc⟩ := mem_iUnion.mp hn
      have hzmem := (b.mem_enclosedSpectrum hp φ hφ _ z _).mpr ⟨hz,hzdisc⟩
      rw [(h.counting.eigenvalue_spec b n hn).1] at hzmem
      exact ⟨n,(h.distant n hn).trans (Finset.mem_singleton.mp hzmem).symm⟩
  · rintro ⟨n,rfl⟩
    by_cases hn : N < n.natAbs
    · rw [h.distant n hn]
      exact (h.counting.eigenvalue_mem_spectrum b n hn).1
    · exact ((b.mem_centralSpectrum hp φ hφ N (ξ n)).mp ((h.central_iff _).mpr ⟨n,by omega,rfl⟩)).1

/-- The range of a complete boundary labeling is closed. -/
theorem isClosed_range (h : BoundaryRootLabeling b hp φ hφ N ξ) : IsClosed (range ξ) := by
  have he : range ξ = b.spectrum hp φ hφ := by ext z; exact (h.exhaustive z).symm
  rw [he]
  exact b.isClosed_spectrum hp φ hφ

/-- Each distant label is an actual simple boundary eigenvalue in its free disc. -/
theorem distant_spec (h : BoundaryRootLabeling b hp φ hφ N ξ) (n : ℤ) (hn : N < n.natAbs) :
    ξ n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧ b.algebraicMultiplicity hp φ hφ (ξ n) = 1 := by
  rw [h.distant n hn]
  exact ⟨(h.counting.eigenvalue_mem_spectrum b n hn).2,(h.counting.eigenvalue_spec b n hn).2⟩

end BoundaryRootLabeling
end NLS.ZakharovShabat
