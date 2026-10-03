import NLS.ZakharovShabat.SourceDirichletSobolevSummability
import NLS.ZakharovShabat.SourceMidpointSobolevSummability

/-! # Both G.7 source derivative estimates on one complex neighborhood

The midpoint derivatives and the Dirichlet derivatives after subtracting
the exact free functional have outer ℓp source operator norms on one open
domain containing the entire real source locus, for finite p≥2.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One common complex domain supports both actual derivative estimates,
including all signed indices and collapsed periodic gaps. -/
theorem exists_global_source_spectral_gradients_sobolev_memlp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion h2p φ)) p ∧
      Memℓp (fun n : ℤ =>
        fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
          (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n) p := by
  obtain ⟨U,hU,hrealU,hmid⟩ := exists_global_source_midpoint_fderiv_sobolev_memlp hp hp1 h2p
  obtain ⟨V,hV,hrealV,hdir⟩ := exists_global_source_dirichlet_fderiv_sobolev_memlp hp hp1 h2p
  refine ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hrealU hφ,hrealV hφ⟩,?_⟩
  intro φ hφ a ha
  exact ⟨hmid φ hφ.1 a ha,hdir φ hφ.2 a ha⟩

end NLS.ZakharovShabat
