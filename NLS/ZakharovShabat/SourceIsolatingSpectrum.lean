import NLS.ZakharovShabat.SourceGlobalIsolation

/-!
# Periodic spectrum inside the source isolating discs

Complete canonical periodic endpoint labels exhaust the actual periodic
spectrum. Pairwise disjoint assigned discs therefore contain exactly the
two endpoints with the matching signed index, including a double root.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- If every canonical cluster lies in its assigned disc and the discs are
pairwise disjoint, the periodic eigenvalues inside one disc are exactly
its own two canonical endpoints. -/
theorem source_periodicSpectrum_in_isolatingDisc_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) {z : ℂ} (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔
      z = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∨
      z = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  constructor
  · intro hspec
    obtain ⟨m, hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
    have hmn : m = n := by
      by_contra hne
      have hzm : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
        rcases hm with hL | hR
        · exact hL ▸ hcluster m (Or.inl rfl)
        · exact hR ▸ hcluster m (Or.inr (Or.inl rfl))
      exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hne)) hz hzm
    subst m
    exact hm.imp Eq.symm Eq.symm
  · intro hroot
    rcases hroot with rfl | rfl
    · exact (canonicalPeriodicEndpoints_mem_spectrum hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).1
    · exact (canonicalPeriodicEndpoints_mem_spectrum hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).2

/-- The full periodic spectrum in an assigned disc is the unordered pair
of canonical endpoints at its index. -/
theorem source_periodicSpectrum_inter_isolatingDisc_eq_pair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    periodicSpectrum hp (periodOnePotential ψ) ∩
      sourceIsolatingDisc hp hp1 φ N ε n =
        {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
         canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} := by
  ext z
  constructor
  · intro hz
    rcases (source_periodicSpectrum_in_isolatingDisc_iff hp hp1 φ ψ N ε
      hcluster hdisjoint n hz.2).mp hz.1 with hL | hR
    · simp [hL]
    · simp [hR]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hL | hR
    · subst z
      exact ⟨(canonicalPeriodicEndpoints_mem_spectrum hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).1,
        hcluster n (Or.inl rfl)⟩
    · subst z
      exact ⟨(canonicalPeriodicEndpoints_mem_spectrum hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).2,
        hcluster n (Or.inr (Or.inl rfl))⟩

end NLS.ZakharovShabat
