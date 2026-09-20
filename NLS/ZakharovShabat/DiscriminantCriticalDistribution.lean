import NLS.ZakharovShabat.DiscriminantCriticalCounts
import NLS.ComplexAnalysis.SimpleAnalyticZero

/-!
# The fixed-potential critical-point distribution

A count of one gives a unique simple critical point strictly inside each distant
free disc. The central disc and the distant discs exhaust all critical points.
The cutoff here depends on a fixed potential; local uniformity and the real-type
conclusion of Lemma 8.3 are not asserted.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A zero-free boundary and count one give a unique simple critical point in the open disc. -/
theorem unique_simple_criticalPoint_of_count (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (r : ℝ)
    (hc : analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall c r) = 1)
    (hb : ∀ z ∈ sphere c r, deriv (canonicalDiscriminant hp φ) z ≠ 0) :
    ∃ x ∈ ball c r, deriv (canonicalDiscriminant hp φ) x = 0 ∧
      analyticOrderAt (deriv (canonicalDiscriminant hp φ)) x = 1 ∧
      ∀ z ∈ closedBall c r, deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = x := by
  obtain ⟨x, hx, hx0, ho, hu⟩ := exists_unique_simple_analytic_zero
    ((analyticOnNhd_discriminant_derivative hp hp1 φ hφ).mono (subset_univ _))
    (fun z _ => analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ z)
    (finite_discriminant_criticalPoints_of_isCompact hp hp1 φ hφ (isCompact_closedBall c r)) hc
  refine ⟨x, ?_, hx0, ho, hu⟩
  rw [mem_ball]
  rcases lt_or_eq_of_le (mem_closedBall.mp hx) with hlt | he
  · exact hlt
  · exact (hb x (mem_sphere.mpr he) hx0).elim

/-- Beyond one cutoff, the central and distant open discs contain every critical point. -/
theorem exists_cutoff_discriminant_critical_exhaustion (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧ ∀ K : ℕ, N ≤ K → ∀ z : ℂ,
      deriv (canonicalDiscriminant hp φ) z = 0 →
      z ∈ ball 0 (centralCircleRadius K) ∨
        ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r := by
  obtain ⟨R, hR⟩ := exists_threshold_critical_mem_freeDisc hp hp1 φ hφ hr hrπ
  obtain ⟨M, hM⟩ := exists_nat_gt (R/Real.pi)
  let N := M+1
  have hN : R ≤ Real.pi*(N : ℝ) := by
    have hM' : R/Real.pi ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith
    exact (div_le_iff₀ Real.pi_pos).mp hM' |>.trans_eq (mul_comm _ _)
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro K hK z hz0
  by_cases hz : z ∈ ball 0 (centralCircleRadius K)
  · exact Or.inl hz
  have hzn : centralCircleRadius K ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz
  have hK' : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hzR : R ≤ ‖z‖ := by unfold centralCircleRadius at hzn; nlinarith [Real.pi_pos]
  obtain ⟨n, hn⟩ := hR z hzR hz0
  refine Or.inr ⟨n, ?_, by simpa only [mem_ball, dist_eq_norm] using hn⟩
  by_contra h
  have hnK : (n.natAbs : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_not_gt h)
  have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have ht := norm_le_norm_sub_add z ((Real.pi : ℂ)*n)
  rw [hnorm] at ht
  unfold centralCircleRadius at hzn
  nlinarith [Real.pi_pos]

/-- The complete fixed-potential counting and exhaustion assertions in Lemma 8.3. -/
theorem exists_discriminant_critical_distribution (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧
      (∀ n : ℤ, N < n.natAbs → ∃ x ∈ ball ((Real.pi : ℂ)*n) r,
        deriv (canonicalDiscriminant hp φ) x = 0 ∧
        analyticOrderAt (deriv (canonicalDiscriminant hp φ)) x = 1 ∧
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          deriv (canonicalDiscriminant hp φ) z = 0 ↔ z = x) ∧
      (∀ K : ℕ, N ≤ K →
        analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
        ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp φ) z ≠ 0) ∧
      (∀ z : ℂ, deriv (canonicalDiscriminant hp φ) z = 0 →
        z ∈ ball 0 (centralCircleRadius N) ∨
        ∃ n : ℤ, N < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r) := by
  obtain ⟨N₁, hN₁, hd, hc⟩ := exists_discriminant_critical_counts hp hp1 φ hφ hr hrπ
  obtain ⟨N₂, _, he⟩ := exists_cutoff_discriminant_critical_exhaustion hp hp1 φ hφ hr hrπ
  refine ⟨max N₁ N₂, hN₁.trans_le (le_max_left _ _), ?_, ?_, he _ (le_max_right _ _)⟩
  · intro n hn
    have h := hd n ((le_max_left N₁ N₂).trans hn.le)
    exact unique_simple_criticalPoint_of_count hp hp1 φ hφ _ r h.1 h.2
  · intro K hK
    exact hc K ((le_max_left _ _).trans hK)

end NLS.ZakharovShabat
