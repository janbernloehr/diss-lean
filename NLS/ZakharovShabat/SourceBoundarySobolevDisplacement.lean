import NLS.ZakharovShabat.ClassicalSobolevBoundaryRootDisplacement
import NLS.ZakharovShabat.SourceDirichletComplexFourierGradient
import NLS.ZakharovShabat.SourceTailIsolation

/-! # Actual canonical boundary displacements at physical H¹ sources

Source tail isolation supplies the quarter-pi discs. Exact physical
characteristic compatibility supplies the zero equation. The inverse-index
bound is therefore derived for the actual indexed roots, uniformly on a
source neighborhood and a physical Sobolev ball.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both canonical boundary sequences have locally uniform inverse-index
H¹ displacement, including complex sources and the original signed indices. -/
theorem exists_local_source_boundary_sobolev_inverse_index_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (ψ₀ : CoeffPair p) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ U →
      ∀ (a : Domain 2), ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ b : BoundaryCondition, ∀ n : ℤ, N ≤ n.natAbs →
        ‖canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n-(Real.pi : ℂ)*n‖ ≤
          B/(n.natAbs : ℝ) := by
  obtain ⟨K,U,hU,hψ₀,hiso⟩ := exists_uniform_source_tail_isolation hp hp1 ψ₀
  obtain ⟨N,hN,B,hB,hbound⟩ := exists_classicalSeparatedRoot_sobolev_inverse_index_bound M hM
  refine ⟨U,hU,hψ₀,max N (K+1),hN.trans_le (le_max_left _ _),B,hB,?_⟩
  intro φ hφ a ha hcompat b n hn
  have hNn := (le_max_left N (K+1)).trans hn
  have hKn : K < n.natAbs := by have := (le_max_right N (K+1)).trans hn; omega
  have hdisc : canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n ∈
      refinedResonantDisk n := by
    have h := hiso _ hφ n hKn
    cases b with
    | dirichlet => exact h.2.2.1
    | neumann => exact h.2.2.2.1
  apply hbound a ha b n hNn
  · exact le_of_lt (by simpa only [refinedResonantDisk,Metric.mem_ball,dist_eq_norm] using hdisc)
  · have he : periodOneBoundaryCharacteristic hp hp1 b (CoeffPair.exponentInclusion h2p φ) =
        classicalSeparatedCharacteristic b (classicalSobolevPotential a) := by
      rw [← periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p b φ]
      exact funext (periodOneBoundaryCharacteristic_eq_classical_of_continuous b φ _
        (physicalBase_source_sobolev_compatibility φ a hcompat))
    rw [← he]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b _ n

end NLS.ZakharovShabat
