import NLS.ZakharovShabat.ClassicalSobolevCriticalRootDisplacement
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.ZakharovShabat.SourceBoundarySobolevDisplacement

/-! # Inverse-index bounds for actual canonical critical points

Exact physical compatibility and the actual critical equation transfer the physical H1 estimate to the canonical signed root labels.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Actual canonical critical points have locally uniform inverse-index
bounds at physical H1 sources, including complex sources and both tails. -/
theorem exists_local_source_critical_sobolev_inverse_index_bound
    (ψ₀ : CoeffPair 2) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ a : Domain 2, ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ n : ℤ, N ≤ n.natAbs →
        ‖canonicalCriticalPoints (by norm_num) (by norm_num) (periodOnePotential φ)
          (periodOnePotential_mem φ) n-(Real.pi:ℂ)*n‖ ≤ B/(n.natAbs:ℝ) := by
  obtain ⟨K,U,hU,hψ₀,hiso⟩ := exists_uniform_source_tail_isolation (by norm_num) (by norm_num) ψ₀
  obtain ⟨N,hN,B,hB,hbound⟩ := exists_classicalCriticalRoot_sobolev_inverse_index_bound M hM
  refine ⟨U,hU,hψ₀,max N (K+1),hN.trans_le (le_max_left _ _),B,hB,?_⟩
  intro φ hφ a ha hcompat n hn
  have hNn := (le_max_left N (K+1)).trans hn
  have hKn : K < n.natAbs := by have := (le_max_right N (K+1)).trans hn; omega
  have hdisc := (hiso φ hφ n hKn).2.2.2.2
  apply hbound a ha n hNn
  · exact le_of_lt (by simpa only [refinedResonantDisk,Metric.mem_ball,dist_eq_norm] using hdisc)
  · have he : canonicalDiscriminant (by norm_num) (periodOnePotential φ) =
        classicalDiscriminant (classicalSobolevPotential a) :=
      funext (canonicalDiscriminant_eq_classical _ (periodOnePotential_mem φ) _
        (physicalBase_source_sobolev_compatibility φ a hcompat))
    rw [← he]
    exact canonicalCriticalPoints_is_critical (by norm_num) (by norm_num) _ (periodOnePotential_mem φ) n

end NLS.ZakharovShabat
