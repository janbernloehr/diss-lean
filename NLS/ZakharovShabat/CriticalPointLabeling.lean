import NLS.ZakharovShabat.CentralCriticalRoots
import NLS.ZakharovShabat.CompletePeriodicParityPairs

/-!
# Complete critical-point labels

The central multiset and the unique simple distant roots give a complete
signed sequence of actual critical points. No continuity or ordering of the
central labels is assumed in this construction.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Central analytic multiplicities, unique simple distant roots, and complete exhaustion. -/
structure CriticalPointLabeling (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (ξ : ℤ → ℂ) : Prop where
  central : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N
  distant : ∀ n : ℤ, N < n.natAbs →
    ξ n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
    deriv (canonicalDiscriminant hp φ) (ξ n) = 0 ∧
    analyticOrderAt (deriv (canonicalDiscriminant hp φ)) (ξ n) = 1 ∧
    ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4), deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = ξ n
  exhaustive : ∀ z : ℂ, deriv (canonicalDiscriminant hp φ) z = 0 ↔ ∃ n : ℤ, ξ n = z

/-- Counts and unique distant roots can be assembled into a complete critical-point labeling. -/
theorem exists_criticalPointLabeling (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ)
    (hd : ∀ n : ℤ, N < n.natAbs → ∃ x ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
      deriv (canonicalDiscriminant hp φ) x = 0 ∧
      analyticOrderAt (deriv (canonicalDiscriminant hp φ)) x = 1 ∧
      ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4), deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = x)
    (hc : analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius N)) = 2*N+1)
    (he : ∀ z : ℂ, deriv (canonicalDiscriminant hp φ) z = 0 →
      z ∈ ball 0 (centralCircleRadius N) ∨ ∃ n : ℤ, N < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4)) :
    ∃ ξ : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N ξ := by
  classical
  obtain ⟨α, hα⟩ := exists_centralCriticalLabeling hp hp1 φ hφ N hc
  let η : ℤ → ℂ := fun n => if hn : N < n.natAbs then (hd n hn).choose else 0
  have hη (n : ℤ) (hn : N < n.natAbs) :
      η n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
      deriv (canonicalDiscriminant hp φ) (η n) = 0 ∧
      analyticOrderAt (deriv (canonicalDiscriminant hp φ)) (η n) = 1 ∧
      ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4), deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = η n := by
    simpa only [η, dif_pos hn] using (hd n hn).choose_spec
  let ξ := spliceCentralRoots N α η
  have hcentral : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N := by
    rw [← hα]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ¬N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
    simp only [ξ, spliceCentralRoots, if_neg hn']
  have hdist (n : ℤ) (hn : N < n.natAbs) :
      ξ n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
      deriv (canonicalDiscriminant hp φ) (ξ n) = 0 ∧
      analyticOrderAt (deriv (canonicalDiscriminant hp φ)) (ξ n) = 1 ∧
      ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4), deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = ξ n := by
    simpa only [ξ, spliceCentralRoots, if_pos hn] using hη n hn
  refine ⟨ξ, ⟨hcentral, hdist, ?_⟩⟩
  intro z
  constructor
  · intro hz
    rcases he z hz with hzcentral | ⟨n, hn, hzn⟩
    · have hzmem := (mem_centralCriticalRoots hp hp1 φ hφ N z).mpr ⟨ball_subset_closedBall hzcentral, hz⟩
      rw [← hcentral] at hzmem
      have hx : ∃ n ∈ Finset.Icc (-(N : ℤ)) N, ξ n = z := by
        simpa only [Multiset.mem_sum, Multiset.mem_singleton, eq_comm] using hzmem
      obtain ⟨n, _, hn⟩ := hx
      exact ⟨n, hn⟩
    · exact ⟨n, ((hdist n hn).2.2.2 z (ball_subset_closedBall hzn)).mp hz |>.symm⟩
  · rintro ⟨n, rfl⟩
    by_cases hn : N < n.natAbs
    · exact (hdist n hn).2.1
    · have hns : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
      have hzmem : ξ n ∈ centralCriticalRoots hp hp1 φ hφ N := by
        rw [← hcentral]
        simp only [Multiset.mem_sum, Multiset.mem_singleton]
        exact ⟨n, hns, rfl⟩
      exact ((mem_centralCriticalRoots hp hp1 φ hφ N _).mp hzmem).2

/-- Every label is an actual critical point. -/
theorem CriticalPointLabeling.is_critical {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p}
    {hφ : φ ∈ pairParitySubspace 0} {N : ℕ} {ξ : ℤ → ℂ}
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (n : ℤ) :
    deriv (canonicalDiscriminant hp φ) (ξ n) = 0 := (h.exhaustive (ξ n)).mpr ⟨n, rfl⟩

end NLS.ZakharovShabat
