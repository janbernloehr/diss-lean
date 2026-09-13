import NLS.ZakharovShabat.CompletePeriodicParityPairs

/-!
# Exact parity spectrum of the completed pair sequences

A completed sequence enumerates precisely the original eigenvalues in its
Fourier parity. The central part uses the counted root multiset; the distant
part uses the original root-space parity theorem and counted spectral pairs.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fourier parity subspaces depend only on the residue modulo two. -/
theorem pairParitySubspace_eq_of_emod_eq (r s : ℤ) (hrs : r % 2 = s % 2) :
    pairParitySubspace (p := p) r = pairParitySubspace s := by
  have he : Coeff.paritySubspace (p := p) r = Coeff.paritySubspace s := by
    ext x
    simp only [Coeff.mem_paritySubspace, hrs]
  simp only [pairParitySubspace, he]

/-- A distant root pair has positive original multiplicity and a root space in its index parity. -/
theorem CompletePeriodicParityPairs.distant_root {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : ξ n = z ∨ η n = z) :
    0 < periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z ∧
      periodicRootSpaceTop hp (weightedBaseToPair w φ) z ≤ pairParitySubspace n := by
  have hm : z ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ)
      ((Real.pi : ℂ)*n) (Real.pi/4) := by
    rw [(h.distant n hn).enclosed_eq]
    simpa [eq_comm] using hz
  obtain ⟨hs, hb⟩ := (mem_enclosedPeriodicSpectrum hp _ _ z _).mp hm
  exact ⟨(periodicAlgebraicMultiplicity_pos_iff hp _ z).mpr hs,
    h.counting.disk_rootSpace_parity h.even_potential n hn z hb⟩

/-- The completed index parity enumerates exactly the eigenvalues with positive parity multiplicity. -/
theorem CompletePeriodicParityPairs.root_iff {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∃ n : ℤ, n % 2 = r % 2 ∧ (ξ n = z ∨ η n = z)) ↔
      0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) r z := by
  constructor
  · rintro ⟨n, hnr, hz⟩
    by_cases hn : N < n.natAbs
    · obtain ⟨hm, hs⟩ := h.distant_root n hn z hz
      rw [pairParitySubspace_eq_of_emod_eq n r hnr] at hs
      rw [parityAlgebraicMultiplicity_eq_of_root_le hp _ r z hs]
      exact hm
    · have hi : n ∈ centralParityIndices N r := by
        simp only [centralParityIndices, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨by omega, hnr⟩
      exact ((h.central.root_iff r hr z).mp ⟨n, hi, hz⟩).2
  · intro hm
    have hf : 0 < periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z := by
      rw [periodicAlgebraicMultiplicity_eq_parity_sum hp _ h.even_potential z]
      rcases hr with rfl | rfl <;> omega
    have hz := (periodicAlgebraicMultiplicity_pos_iff hp _ z).mp hf
    rcases (h.counting.mem_spectrum_iff_central_or_disk z).mp hz with hc | ⟨n, ⟨hn, hd⟩, _⟩
    · obtain ⟨n, hi, he⟩ := (h.central.root_iff r hr z).mpr ⟨hc, hm⟩
      exact ⟨n, (Finset.mem_filter.mp hi).2, he⟩
    · have hs := h.counting.disk_rootSpace_parity h.even_potential n hn z
        ((mem_enclosedPeriodicSpectrum hp _ _ z _).mp hd).2
      have hnr : n % 2 = r % 2 := by
        by_contra he
        have hm0 := parityAlgebraicMultiplicity_eq_zero_of_root_le hp _ r n z (Ne.symm he) hs
        omega
      refine ⟨n, hnr, ?_⟩
      rw [(h.distant n hn).enclosed_eq] at hd
      simpa [eq_comm] using hd

/-- The completed sequences therefore enumerate exactly the original domain eigenvalues of each parity. -/
theorem CompletePeriodicParityPairs.root_iff_domain_eigenvector {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∃ n : ℤ, n % 2 = r % 2 ∧ (ξ n = z ∨ η n = z)) ↔
      ∃ f : Domain p, f ≠ 0 ∧ f ∈ domainParitySubspace r ∧
        spectralPencil hp (weightedBaseToPair w φ) z f = 0 :=
  (h.root_iff r hr z).trans (parityAlgebraicMultiplicity_pos_iff hp _ h.even_potential r z)

end NLS.ZakharovShabat
