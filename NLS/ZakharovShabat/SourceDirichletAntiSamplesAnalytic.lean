import NLS.ZakharovShabat.SourceLemma9_2
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Banach analytic actual Dirichlet anti-discriminant samples

Scalar root analyticity and Lemma 9.2's local full sequence bounds
assemble the actual samples on one neighborhood of every real source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem analyticOnNhd_sourceDirichletAntiDiscriminantSamples_of_roots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (hW : IsOpen W)
    (hroots : ∀ n : ℤ, AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) W) :
    AnalyticOnNhd ℂ (sourceDirichletAntiDiscriminantSamples hp hp1) W := by
  intro φ hφ
  obtain ⟨U,hU,hφU,K,_,hdata⟩ := sourceLemma9_2 hp hp1 φ
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => sourceDirichletAntiDiscriminantSamples hp hp1 ψ n) (W ∩ U) := by
    intro ψ hψ
    exact (hdata.analytic _ (mem_univ _)).comp
      (f := fun χ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n,χ))
      ((hroots n ψ hψ.1).prod analyticAt_id)
  exact (Coeff.analyticOnNhd_of_bounded_coordinatewise _ (hW.inter hU) hcoord K
    (fun ψ hψ => hdata.value_norm ψ hψ.2)) φ ⟨hφ,hφU⟩

theorem exists_sourceDirichletAntiDiscriminantSamples_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      AnalyticOnNhd ℂ (sourceDirichletAntiDiscriminantSamples hp hp1) W := by
  obtain ⟨W,hW,hreal,hroots⟩ := exists_sourceBoundaryRoots_analytic_common_domain hp hp1
  exact ⟨W,hW,hreal,analyticOnNhd_sourceDirichletAntiDiscriminantSamples_of_roots
    hp hp1 W hW (hroots .dirichlet)⟩

end NLS.ZakharovShabat
