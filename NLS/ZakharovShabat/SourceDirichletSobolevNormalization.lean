import NLS.ZakharovShabat.SourceBoundarySobolevDisplacement
import NLS.ZakharovShabat.ClassicalDirichletNormalizationBounds

/-! # Uniform normalization of actual high-index Dirichlet eigenfunctions

The canonical root displacement and bilinear normalization estimates share
one cutoff and source neighborhood. Their constants are uniform on the
physical H¹ ball. All geometric and nonvanishing facts are derived.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both boundary displacements and the actual Dirichlet normalization have
uniform inverse-index bounds on a source neighborhood and a physical H¹ ball.
The normalization is bounded below by one and its inverse approaches one half. -/
theorem exists_local_source_dirichlet_sobolev_normalization_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ψ₀ : CoeffPair p) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧
      ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ U →
      ∀ (a : Domain 2), ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ n : ℤ, N ≤ n.natAbs →
        (∀ b : BoundaryCondition,
          ‖canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n-(Real.pi : ℂ)*n‖ ≤
            B/(n.natAbs : ℝ)) ∧
        let Q := classicalDirichletNormalization (classicalSobolevPotential a)
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
        ‖Q-2‖ ≤ C/(n.natAbs : ℝ) ∧ 1 ≤ ‖Q‖ ∧ ‖Q⁻¹‖ ≤ 1 ∧
          ‖Q⁻¹-(2 : ℂ)⁻¹‖ ≤ C/(2*(n.natAbs : ℝ)) := by
  obtain ⟨U,hU,hψ₀,N,hN,B,hB,hdisp⟩ :=
    exists_local_source_boundary_sobolev_inverse_index_bound hp hp1 h2p ψ₀ M hM
  obtain ⟨K,_,C,hC,hQ⟩ := exists_classicalDirichletNormalization_near_free_bounds M B hM hB
  refine ⟨U,hU,hψ₀,max N K,hN.trans_le (le_max_left _ _),B,C,hB,hC,?_⟩
  intro φ hφ a ha hcompat n hn
  have hnN := (le_max_left N K).trans hn
  have hnK := (le_max_right N K).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hN.trans_le hnN
  have hd := hdisp φ hφ a ha hcompat
  refine ⟨fun b => hd b n hnN,?_⟩
  exact hQ a ha n hnK _ ((hd .dirichlet n hnN).trans (div_le_self hB hn1))

end NLS.ZakharovShabat
