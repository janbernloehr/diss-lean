import NLS.ComplexAnalysis.Rouche

/-!
# Computing and transporting scalar zero counts

The count depends only on which zeros a set contains. A centered monomial
has its degree as count in every set containing its center, and Rouché
transfers that count to a strict boundary perturbation.
-/

noncomputable section
open Metric
open scoped Classical
namespace NLS.ComplexAnalysis

/-- Sets containing the same zeros have the same scalar analytic zero count. -/
theorem analyticZeroCount_congr_set (f : ℂ → ℂ) {K L : Set ℂ}
    (h : ∀ z, f z = 0 → (z ∈ K ↔ z ∈ L)) : analyticZeroCount f K = analyticZeroCount f L := by
  unfold analyticZeroCount
  congr 1
  funext z
  by_cases hz : f z = 0
  · simp only [h z hz]
  · have hn : analyticOrderNatAt f z = 0 := by
      by_contra hn
      exact hz (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)
    simp [hn]

/-- A centered monomial contributes exactly its degree, including a repeated root. -/
theorem analyticZeroCount_centeredMonomial (c : ℂ) (n : ℕ) {K : Set ℂ} (hc : c ∈ K) :
    analyticZeroCount (fun z => (z-c)^n) K = n := by
  rw [analyticZeroCount_eq_sum {c} (by simpa using hc) ?_]
  · simp only [Finset.sum_singleton]
    change (analyticOrderAt ((· - c) ^ n) c).toNat = n
    rw [analyticOrderAt_centeredMonomial]
    simp
  · intro z hz
    simpa only [Finset.mem_coe, Finset.mem_singleton] using sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz.2)

/-- A strict perturbation of a centered monomial has exactly its degree many analytic zeros. -/
theorem analyticZeroCount_eq_degree_of_boundary_lt {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (h : ∀ z ∈ sphere c R, ‖f z-(z-c)^n‖ < ‖(z-c)^n‖) :
    analyticZeroCount f (closedBall c R) = n := by
  rw [analyticZeroCount_eq_of_boundary_lt hR (by intro z _; fun_prop) hf h]
  exact analyticZeroCount_centeredMonomial c n (mem_closedBall_self hR.le)

/-- With a nonvanishing boundary, open and closed discs have the same zero count. -/
theorem analyticZeroCount_ball_eq_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    analyticZeroCount f (ball c R) = analyticZeroCount f (closedBall c R) := by
  apply analyticZeroCount_congr_set
  intro z hz
  exact ⟨fun h => ball_subset_closedBall h, fun h => lt_of_le_of_ne h (fun he => hb z he hz)⟩

end NLS.ComplexAnalysis
