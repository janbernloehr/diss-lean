import NLS.ZakharovShabat.SourceDirichletSobolevNormalization
import NLS.ZakharovShabat.ClassicalDirichletGradientValueBounds

/-! # Uniform pointwise free-wave error at actual source Dirichlet roots

Root displacement and normalization estimates are instantiated at the
canonical signed roots. The resulting physical gradient error is uniform
on a source neighborhood, the H¹ ball, and the whole time interval.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The normalized gradient at the actual canonical Dirichlet root differs
from the two exact free waves by O(1/|n|), uniformly in time and on H¹ balls. -/
theorem exists_local_source_dirichlet_gradient_value_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ψ₀ : CoeffPair p) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ U →
      ∀ (a : Domain 2), ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ t : Icc (0 : ℝ) 1,
        ‖classicalDirichletNormalizedGradient (classicalSobolevPotential a)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) t-
          (exp (2*I*((Real.pi : ℂ)*n)*t.val)/2,exp (-2*I*((Real.pi : ℂ)*n)*t.val)/2)‖ ≤
          D/(n.natAbs : ℝ) := by
  obtain ⟨U,hU,hψ₀,N,hN,B,C,hB,hC,hbounds⟩ :=
    exists_local_source_dirichlet_sobolev_normalization_bounds hp hp1 h2p ψ₀ M hM
  obtain ⟨K,hK⟩ := exists_nat_ge (max B C)
  let D := 2*Real.exp (4*M+B)*(classicalSobolevErrorConstant M B+2*B)+C/2
  have hD : 0 ≤ D := by
    have he := classicalSobolevErrorConstant_nonneg M B hM
    dsimp [D]
    positivity
  refine ⟨U,hU,hψ₀,max N K,hN.trans_le (le_max_left _ _),D,hD,?_⟩
  intro φ hφ a ha hcompat n hn t
  have hnN := (le_max_left N K).trans hn
  have hnK : (K : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast (le_max_right N K).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hN.trans_le hnN
  have hBn := (le_max_left B C).trans (hK.trans hnK)
  have hCn := (le_max_right B C).trans (hK.trans hnK)
  obtain ⟨hdisp,hQ,_,_,_⟩ := hbounds φ hφ a ha hcompat n hnN
  have hQ1 := hQ.trans ((div_le_one (lt_of_lt_of_le zero_lt_one hn1)).mpr hCn)
  rw [← classicalDirichletNormalizedGradient_free ((Real.pi : ℂ)*n) t]
  exact norm_classicalDirichletNormalizedGradient_sub_free_sobolev_le M B C hB a ha n hn1 hBn _
    (hdisp .dirichlet) hQ1 hQ t

end NLS.ZakharovShabat
