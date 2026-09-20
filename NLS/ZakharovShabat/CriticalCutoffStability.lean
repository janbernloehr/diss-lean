import NLS.ZakharovShabat.CriticalPointMultiplicity

/-!
# Stability of complete critical labels under increasing cutoffs

A larger central disc contains exactly the labels at the larger central
index set. Their global analytic multiplicities recover its multiset, so
the same complete sequence remains valid at every larger cutoff.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- A label lies in a larger central disc exactly when its index lies in that central block. -/
theorem CriticalPointLabeling.mem_larger_central_iff (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (K : ℕ) (hK : N ≤ K) (n : ℤ) :
    ξ n ∈ closedBall 0 (centralCircleRadius K) ↔ n.natAbs ≤ K := by
  constructor
  · intro hz
    by_contra hn
    have hfar : K < n.natAbs := by omega
    exact notMem_central_of_mem_distant_criticalDisc K n hfar (ξ n)
      (h.distant n (by omega)).1 hz
  · intro hn
    by_cases hnN : n.natAbs ≤ N
    · apply closedBall_subset_closedBall _ (h.central_mem n hnN)
      unfold centralCircleRadius
      exact add_le_add (mul_le_mul_of_nonneg_right
        (show (N : ℝ) ≤ (K : ℝ) by exact_mod_cast hK) Real.pi_pos.le) le_rfl
    · have hd : ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
        simpa only [mem_ball, dist_eq_norm] using (h.distant n (by omega)).1
      have hc : ‖(Real.pi : ℂ)*n‖ ≤ Real.pi*K := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        rw [← Int.cast_abs, ← Int.natCast_natAbs]
        exact_mod_cast hn
      have ht := norm_le_norm_sub_add (ξ n) ((Real.pi : ℂ)*n)
      simp only [mem_closedBall, dist_zero_right]
      unfold centralCircleRadius
      nlinarith [Real.pi_pos]

/-- The labels in every larger central block give its exact root multiset. -/
theorem CriticalPointLabeling.central_at_larger_cutoff (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (K : ℕ) (hK : N ≤ K) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) K, ({ξ n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ K := by
  apply Multiset.ext.mpr
  intro z
  rw [Multiset.count_sum', count_centralCriticalRoots]
  by_cases hz : z ∈ closedBall 0 (centralCircleRadius K)
  · rw [if_pos hz, ← h.multiplicity z]
    have hs : Function.support (fun n : ℤ => if ξ n = z then (1 : ℕ) else 0) ⊆
        (Finset.Icc (-(K : ℤ)) K : Set ℤ) := by
      intro n hn
      have he : ξ n = z := by
        simpa only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hn
      have hnK := (h.mem_larger_central_iff K hK n).mp (by rw [he]; exact hz)
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    rw [finsum_eq_sum_of_support_subset _ hs]
    simp only [Multiset.count_singleton, eq_comm]
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro n hn
    have hnK : n.natAbs ≤ K := by simp only [Finset.mem_Icc] at hn; omega
    have he : ξ n ≠ z := fun he => hz (he ▸ (h.mem_larger_central_iff K hK n).mpr hnK)
    simp only [Multiset.count_singleton, if_neg (Ne.symm he)]

/-- Enlarging the central cutoff preserves the complete critical labeling without changing any root. -/
theorem CriticalPointLabeling.enlarge (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (K : ℕ) (hK : N ≤ K) : CriticalPointLabeling hp hp1 φ hφ K ξ :=
  ⟨h.central_at_larger_cutoff K hK, fun n hn => h.distant n (by omega), h.exhaustive⟩

end NLS.ZakharovShabat
