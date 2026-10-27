import NLS.ZakharovShabat.PhysicalSignedUniformCircleCounts
import NLS.ZakharovShabat.PhysicalSignedUniformEnumeration

/-! # The locally uniform signed spectral statement at the opening of Section 7 -/
noncomputable section
set_option autoImplicit false
open Metric Set
namespace NLS.ZakharovShabat

/-- Section 7's literal central-circle counts and distant parity assignment hold
on one common physical L² neighborhood for arbitrary complex potentials. Counts
are actual full generalized-eigenspace dimensions; the distant combined labels
also agree with the independently ordered signed lists. -/
theorem exists_uniform_physicalSignedSpectralOverview (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      ∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N →
        sphere (0 : ℂ) ((2*(N : ℝ)+1/2)*Real.pi) ⊆
          classicalSignedResolventSet v 0 ∩ classicalSignedResolventSet v 1 ∧
        (∑ z ∈ enclosedClassicalSignedSpectrum v 0 0 ((2*(N : ℝ)+1/2)*Real.pi),
          classicalSignedAlgebraicMultiplicity v 0 z) = 4*N+2 ∧
        (∑ z ∈ enclosedClassicalSignedSpectrum v 1 0 ((2*(N : ℝ)+1/2)*Real.pi),
          classicalSignedAlgebraicMultiplicity v 1 z) = 4*N ∧
        ∀ r : Fin 2, ∀ n : ℤ, N < n.natAbs →
          physicalSignedLeft v r n = physicalPeriodicLeft v (2*n+(r.val : ℤ)) ∧
          physicalSignedRight v r n = physicalPeriodicRight v (2*n+(r.val : ℤ)) ∧
          physicalPeriodicLeft v (2*n+(r.val : ℤ)) ∈ classicalSignedSpectrum v (r.val : ℤ) ∧
          physicalPeriodicRight v (2*n+(r.val : ℤ)) ∈ classicalSignedSpectrum v (r.val : ℤ) := by
  obtain ⟨K,hK,V,hoV,hcV,huV,h0V,hV⟩ := exists_uniform_physicalSignedCircleCounts u
  obtain ⟨L,_,W,hoW,hcW,huW,h0W,hW⟩ := exists_uniform_physicalSignedPairs_eq_periodic u
  refine ⟨max K L,by omega,V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨huV,huW⟩,⟨h0V,h0W⟩,?_⟩
  intro v hv N hN
  have hcounts := hV v hv.1 N (by omega)
  refine ⟨fun z hz => ⟨(hcounts 0).1 hz,(hcounts 1).1 hz⟩,?_,?_,?_⟩
  · simpa only [Int.zero_emod,ite_true] using (hcounts 0).2
  · simpa only [show (1 : ℤ) % 2 = 1 by norm_num,show ¬(1 : ℤ) = 0 by norm_num,ite_false]
      using (hcounts 1).2
  · intro r n hn
    have he := hW v hv.2 N (by omega) r n hn
    refine ⟨he.1,he.2,?_,?_⟩
    · rw [← he.1]
      exact (physicalSignedPairs_exhaustive v r _).mpr ⟨n,Or.inl rfl⟩
    · rw [← he.2]
      exact (physicalSignedPairs_exhaustive v r _).mpr ⟨n,Or.inr rfl⟩

end NLS.ZakharovShabat
