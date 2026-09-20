import NLS.ZakharovShabat.CriticalPointLabeling

/-!
# Exact multiplicities of the complete critical-point sequence

Distant free discs are disjoint from one another and from the central disc.
Thus the central multiset and simple distant roots give the correct global
analytic multiplicity at every spectral point.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A distant quarter-pi disc lies strictly outside the central closed disc. -/
theorem notMem_central_of_mem_distant_criticalDisc (N : ℕ) (n : ℤ) (hn : N < n.natAbs)
    (z : ℂ) (hz : z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4)) : z ∉ closedBall 0 (centralCircleRadius N) := by
  intro hcentral
  have hzN : ‖z‖ ≤ centralCircleRadius N := by simpa using hcentral
  have hzd : ‖z-(Real.pi : ℂ)*n‖ < Real.pi/4 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hfree : Real.pi*((N : ℝ)+1) ≤ ‖(Real.pi : ℂ)*n‖ := by
    calc
      _ ≤ Real.pi*(n.natAbs : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hn) Real.pi_pos.le
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast,
          Nat.cast_natAbs, Int.cast_abs]
  have ht := norm_le_norm_sub_add ((Real.pi : ℂ)*n) z
  rw [norm_sub_rev] at ht
  unfold centralCircleRadius at hzN
  nlinarith [Real.pi_pos]

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Central labels lie in the central closed disc. -/
theorem CriticalPointLabeling.central_mem (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (n : ℤ) (hn : n.natAbs ≤ N) : ξ n ∈ closedBall 0 (centralCircleRadius N) := by
  have hns : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
  have hm : ξ n ∈ centralCriticalRoots hp hp1 φ hφ N := by
    rw [← h.central]
    simp only [Multiset.mem_sum, Multiset.mem_singleton]
    exact ⟨n, hns, rfl⟩
  exact ((mem_centralCriticalRoots hp hp1 φ hφ N _).mp hm).1

/-- A distant root occurs at only its own signed index. -/
theorem CriticalPointLabeling.eq_index_of_distant (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (n : ℤ) (hn : N < n.natAbs) (m : ℤ) (he : ξ m = ξ n) : m = n := by
  have hdn := (h.distant n hn).1
  by_cases hm : N < m.natAbs
  · by_contra hmn
    exact (periodicDisks_disjoint m n hmn).le_bot ⟨(h.distant m hm).1, by rw [he]; exact hdn⟩
  · have hc := h.central_mem m (by omega)
    rw [he] at hc
    exact (notMem_central_of_mem_distant_criticalDisc N n hn (ξ n) hdn hc).elim

/-- The global sequence lists every critical point exactly as often as its analytic order. -/
theorem CriticalPointLabeling.multiplicity (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (z : ℂ) :
    (∑ᶠ n : ℤ, if ξ n = z then (1 : ℕ) else 0) = analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z := by
  by_cases hz : z ∈ closedBall 0 (centralCircleRadius N)
  · rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(N : ℤ)) N) (by
      intro n hn
      have hξz : ξ n = z := by simpa only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hn
      have hi : n.natAbs ≤ N := by
        by_contra hn'
        have hd := notMem_central_of_mem_distant_criticalDisc N n (by omega) (ξ n) (h.distant n (by omega)).1
        exact hd (by rw [hξz]; exact hz)
      simp only [Finset.mem_coe, Finset.mem_Icc]
      omega)]
    have hc := congrArg (Multiset.count z) h.central
    rw [count_centralCriticalRoots, if_pos hz] at hc
    simpa only [Multiset.count_sum', Multiset.count_singleton, eq_comm] using hc
  · by_cases hroot : deriv (canonicalDiscriminant hp φ) z = 0
    · obtain ⟨n, hn⟩ := (h.exhaustive z).mp hroot
      have hfar : N < n.natAbs := by
        by_contra hlow
        exact hz (hn ▸ h.central_mem n (by omega))
      rw [finsum_eq_single _ n (by
        intro m hmn
        have hne : ξ m ≠ z := fun hm => hmn (h.eq_index_of_distant n hfar m (hm.trans hn.symm))
        simp only [if_neg hne]), if_pos hn]
      have ho := (h.distant n hfar).2.2.1
      rw [hn] at ho
      simp only [analyticOrderNatAt, ho, ENat.toNat_one]
    · have he (n : ℤ) : ξ n ≠ z := fun hn => hroot (hn ▸ h.is_critical n)
      simp only [if_neg (he _), finsum_zero]
      symm
      by_contra ho
      exact hroot (apply_eq_zero_of_analyticOrderNatAt_ne_zero ho)

end NLS.ZakharovShabat
