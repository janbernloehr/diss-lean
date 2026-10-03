import NLS.ZakharovShabat.SourceDirichletGradientValueBound
import NLS.ZakharovShabat.ClassicalDirichletGradientDerivativeBound

/-! # Uniform time bounds at the actual canonical Dirichlet roots

A common source neighborhood and tail cutoff give both the inverse-index
value error and a bounded derivative, uniformly on physical H¹ balls.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both inputs for Fourier interpolation hold uniformly for the actual
normalized Dirichlet gradient error at nearby complex H¹ sources. -/
theorem exists_local_source_dirichlet_gradient_time_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ψ₀ : CoeffPair p) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧
      ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ U →
      ∀ (a : Domain 2), ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ t : Icc (0 : ℝ) 1,
        let R := classicalDirichletGradientError (classicalSobolevPotential a)
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
          ((Real.pi : ℂ)*n)
        ‖R t‖ ≤ A/(n.natAbs : ℝ) ∧ ‖deriv R t‖ ≤ D := by
  obtain ⟨U,hU,hψU,N,hN,A,hA,hvalue⟩ :=
    exists_local_source_dirichlet_gradient_value_bound hp hp1 h2p ψ₀ M hM
  obtain ⟨V,hV,hψV,K,hK,B,C,hB,_,hnorm⟩ :=
    exists_local_source_dirichlet_sobolev_normalization_bounds hp hp1 h2p ψ₀ M hM
  let D := 2*(Real.pi+B)*A+2*B+8*M*(Real.exp (4*M+B))^2
  refine ⟨U ∩ V,hU.inter hV,⟨hψU,hψV⟩,max N K,hN.trans_le (le_max_left _ _),A,D,hA,?_,?_⟩
  · dsimp [D]; positivity
  intro φ hφ a ha hcompat n hn t
  have hnN := (le_max_left N K).trans hn
  have hnK := (le_max_right N K).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hK.trans_le hnK
  obtain ⟨hdisp,_,_,hinv,_⟩ := hnorm φ hφ.2 a ha hcompat n hnK
  have hv := hvalue φ hφ.1 a ha hcompat n hnN t
  rw [← classicalDirichletNormalizedGradient_free ((Real.pi : ℂ)*n) t] at hv
  exact ⟨hv,norm_deriv_classicalDirichletGradientError_sobolev_le M B A hB a ha n hn1 _
    (hdisp .dirichlet) hinv t hv⟩

end NLS.ZakharovShabat
