import NLS.ZakharovShabat.SourceTailIsolation
import NLS.ZakharovShabat.FreeDiscSeparation

open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n ∧
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ refinedResonantDisk n ∧
        canonicalPeriodOneBoundaryRoots hp hp1 .neumann ψ n ∈ refinedResonantDisk n ∧
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
          refinedResonantDisk n :=
  exists_uniform_source_tail_isolation hp hp1 φ

example {m n : ℤ} (hmn : m ≠ n) {z w : ℂ}
    (hz : z ∈ refinedResonantDisk m) (hw : w ∈ refinedResonantDisk n) :
    (Real.pi/2)*|((m-n : ℤ) : ℝ)| ≤ dist z w ∧
      dist z w ≤ (3*Real.pi/2)*|((m-n : ℤ) : ℝ)| :=
  refinedResonantDisk_pointwise_separation hmn hz hw

example {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (refinedResonantDisk m) (refinedResonantDisk n) :=
  refinedResonantDisk_disjoint hmn

end NLS.ZakharovShabat
