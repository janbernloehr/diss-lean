import NLS.ZakharovShabat.SourcePeriodicTailIsolation
import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.ZakharovShabat.UniformCanonicalBoundaryRoots
import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryRoots

/-!
# Common high-index isolating discs on the source space

The first geometric requirement of Lemma 10.1 uses one cutoff and one
source neighborhood for the periodic endpoints, both ordinary boundary
roots, and the critical point at each distant signed index.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All five canonical spectral coordinates at a sufficiently distant index
lie in the same free quarter-π disc on one open source neighborhood. -/
theorem exists_uniform_source_tail_isolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n ∧
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ refinedResonantDisk n ∧
        canonicalPeriodOneBoundaryRoots hp hp1 .neumann ψ n ∈ refinedResonantDisk n ∧
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n := by
  let F := periodOnePotential (p := p)
  let G := periodOneBoundaryPotential hp hp1
  obtain ⟨Np, Up, hUpo, hUpφ, hperiod⟩ :=
    exists_uniform_source_periodic_tail_isolation hp hp1 φ
  obtain ⟨Nc, _, Uc, hUco, _, hUcφ, _, _, _, hcritical⟩ :=
    exists_uniform_canonicalCriticalPoints_all_cutoffs hp hp1 (F φ)
  obtain ⟨Nb, _, Ub, hUbo, _, hUbφ, _, _, _, hboundary⟩ :=
    exists_uniform_canonicalBoundaryRoots_all_cutoffs hp hp1 (G φ)
  let N := max Np (max Nc Nb)
  let U := (Up ∩ (F ⁻¹' Uc)) ∩ (G ⁻¹' Ub)
  refine ⟨N, U,
    (hUpo.inter (hUco.preimage F.continuous)).inter (hUbo.preimage G.continuous),
    ⟨⟨hUpφ,hUcφ⟩,hUbφ⟩, ?_⟩
  intro ψ hψ n hn
  have hP := hperiod ψ hψ.1.1 n ((le_max_left Np (max Nc Nb)).trans_lt hn)
  have hC := (hcritical (F ψ) hψ.1.2 (periodOnePotential_mem ψ)).2 N
    ((le_max_left Nc Nb).trans (le_max_right Np (max Nc Nb)))
  have hBD := (hboundary (G ψ) hψ.2 .dirichlet).1 N
    ((le_max_right Nc Nb).trans (le_max_right Np (max Nc Nb)))
  have hBN := (hboundary (G ψ) hψ.2 .neumann).1 N
    ((le_max_right Nc Nb).trans (le_max_right Np (max Nc Nb)))
  exact ⟨hP.1, hP.2,
    (by simpa only [canonicalPeriodOneBoundaryRoots, refinedResonantDisk] using
      (hBD.distant_spec n hn).1),
    (by simpa only [canonicalPeriodOneBoundaryRoots, refinedResonantDisk] using
      (hBN.distant_spec n hn).1),
    (hC.distant n hn).1⟩

end NLS.ZakharovShabat
